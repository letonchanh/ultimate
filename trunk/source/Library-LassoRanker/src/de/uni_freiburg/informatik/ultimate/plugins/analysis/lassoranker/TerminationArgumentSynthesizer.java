/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates.RankingFunctionTemplate;


/**
 * This is the synthesizer that generates ranking functions.
 * 
 * @author Jan Leike
 */
public class TerminationArgumentSynthesizer extends ArgumentSynthesizer {
	/**
	 * List of supporting invariant generators used by the last synthesize()
	 * call
	 */
	private final Collection<SupportingInvariantGenerator> m_si_generators;
	
	/**
	 * Number of Motzkin's Theorem applications used by the last synthesize()
	 * call
	 */
	private int m_num_motzkin = 0;
	
	// Objects resulting from the synthesis process
	private RankingFunction m_ranking_function = null;
	private Collection<SupportingInvariant> m_supporting_invariants = null;
	
	private final RankingFunctionTemplate m_template;
	
	/**
	 * Constructor for the termination argument function synthesizer.
	 * @param stem the stem transition, may be null
	 * @param loop the loop transition
	 * @param template the ranking function template to be used in the analysis
	 * @param preferences arguments to the synthesis process
	 */
	public TerminationArgumentSynthesizer(LinearTransition stem,
			LinearTransition loop, RankingFunctionTemplate template,
			Preferences preferences) {
		super(stem, loop, preferences, template.getName() + "Template");
		m_template = template;
		
		m_si_generators = new ArrayList<SupportingInvariantGenerator>();
		m_supporting_invariants = new ArrayList<SupportingInvariant>();
		
		// Set logic
		if (preferences.termination_check_nonlinear) {
			m_script.setLogic(Logics.QF_NRA);
		} else {
			m_script.setLogic(Logics.QF_LRA);
		}
	}
	
	/**
	 * @return RankVar's that are relevant for supporting invariants
	 */
	public Collection<RankVar> getSIVars() {
		/*
		 * Variables that occur as outVars of the stem but are not read by the
		 * loop (i.e., do not occur as inVar of the loop) are not relevant for
		 * supporting invariants.
		 */
		if (m_stem == null) {
			return Collections.emptyList();
		}
		Set<RankVar> result =
				new LinkedHashSet<RankVar>(m_stem.getOutVars().keySet());
		result.retainAll(m_loop.getInVars().keySet());
		return result;
	}
	
	/**
	 * @return RankVar's that are relevant for ranking functions
	 */
	public Collection<RankVar> getRankVars() {
		Collection<RankVar> vars = 
				new LinkedHashSet<RankVar>(m_loop.getOutVars().keySet());
		vars.retainAll(m_loop.getInVars().keySet());
		return vars;
	}
	
	/**
	 * Use the ranking template to build the constraints whose solution gives
	 * the termination argument
	 * @param template the ranking function template
	 * @param si_generators Output container for the used SI generators
	 * @return List of all conjuncts of the constraints
	 */
	private Collection<Term> buildConstraints(RankingFunctionTemplate template,
			Collection<SupportingInvariantGenerator> si_generators) {
		List<Term> conj = new ArrayList<Term>(); // List of constraints
		
		Collection<RankVar> siVars = getSIVars();
		List<List<LinearInequality>> templateConstraints =
				template.getConstraints(m_loop.getInVars(),
						m_loop.getOutVars());
		List<String> annotations = template.getAnnotations();
		assert annotations.size() == templateConstraints.size();
		
		s_Logger.info("We have " + m_loop.getNumPolyhedra()
				+ " loop disjuncts and " + templateConstraints.size()
				+ " template conjuncts.");
		
		// Negate template inequalities
		for (List<LinearInequality> templateDisj : templateConstraints) {
			for (LinearInequality li : templateDisj) {
				li.negate();
			}
		}
		
		// loop(x, x') /\ si(x) -> template(x, x')
		// Iterate over the loop conjunctions and template disjunctions
		int j = 0;
		for (List<LinearInequality> loopConj : m_loop.getPolyhedra()) {
			++j;
			for (int m = 0; m < templateConstraints.size(); ++m) {
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script,
								!m_preferences.termination_check_nonlinear,
								m_preferences.annotate_terms);
				motzkin.annotation = annotations.get(m) + " " + j;
				motzkin.add_inequalities(loopConj);
				motzkin.add_inequalities(templateConstraints.get(m));
				
				// Add supporting invariants
				assert(m_preferences.num_strict_invariants >= 0);
				for (int i = 0; i < m_preferences.num_strict_invariants; ++i) {
					SupportingInvariantGenerator sig =
							new SupportingInvariantGenerator(m_script, siVars,
									true);
					si_generators.add(sig);
					motzkin.add_inequality(sig.generate(m_loop.getInVars()));
				}
				assert(m_preferences.num_non_strict_invariants >= 0);
				for (int i = 0; i < m_preferences.num_non_strict_invariants;
						++i) {
					SupportingInvariantGenerator sig =
							new SupportingInvariantGenerator(m_script, siVars,
									false);
					si_generators.add(sig);
					LinearInequality li = sig.generate(m_loop.getInVars());
					li.motzkin_coefficient_can_be_zero = false;
					motzkin.add_inequality(li);
				}
				s_Logger.debug(motzkin);
				conj.add(motzkin.transform());
			}
		}
		
		// Add constraints for the supporting invariants
		s_Logger.debug("Adding the constraints for " + si_generators.size()
				+ " supporting invariants.");
		int i = 0;
		for (SupportingInvariantGenerator sig : si_generators) {
			++i;
			
			// stem(x0) -> si(x0)
			j = 0;
			for (List<LinearInequality> stemConj : m_stem.getPolyhedra()) {
				++j;
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script,
								!m_preferences.termination_check_nonlinear,
								m_preferences.annotate_terms);
				motzkin.annotation = "invariant " + i + " initiation " + j;
				motzkin.add_inequalities(stemConj);
				LinearInequality li = sig.generate(m_stem.getOutVars());
				li.negate();
				li.motzkin_coefficient_can_be_zero = false;
					// otherwise the stem is unsat
				motzkin.add_inequality(li);
				conj.add(motzkin.transform());
			}
			
			// si(x) /\ loop(x, x') -> si(x')
			j = 0;
			for (List<LinearInequality> loopConj : m_loop.getPolyhedra()) {
				++j;
				MotzkinTransformation motzkin =
						new MotzkinTransformation(m_script,
								!m_preferences.termination_check_nonlinear,
								m_preferences.annotate_terms);
				motzkin.annotation = "invariant " + i + " consecution " + j;
				motzkin.add_inequalities(loopConj);
				motzkin.add_inequality(sig.generate(m_loop.getInVars())); // si(x)
				LinearInequality li = sig.generate(m_loop.getOutVars()); // ~si(x')
				li.needs_motzkin_coefficient =
						!m_preferences.only_nondecreasing_invariants;
				li.negate();
				motzkin.add_inequality(li);
				conj.add(motzkin.transform());
			}
		}
		return conj;
	}
	
	/**
	 * Ranking function generation for lasso programs
	 * 
	 * This procedure is complete in the sense that if there is a linear ranking
	 * function that can be derived with a linear supporting invariant of the
	 * form si(x) >= 0, then it will be found by this procedure.
	 * 
	 * Iff a ranking function is found, this method returns true and the
	 * resulting ranking function and supporting invariant can be retrieved
	 * using the methods getRankingFunction() and getSupportingInvariant().
	 * 
	 * @param template the ranking template to be used
	 * @return SAT if a termination argument was found, UNSAT if existence of
	 *  a termination argument was refuted, UNKNOWN if the solver was not able
	 *  to decide existence of a termination argument
	 * @throws SMTLIBException error with the SMT solver
	 * @throws TermException if the supplied transitions contain
	 *          non-affine update statements
	 */
	@Override
	protected LBool do_synthesis() throws SMTLIBException, TermException {
		if (!m_preferences.termination_check_nonlinear
				&& m_template.getDegree() > 0) {
			s_Logger.warn("Using a linear SMT query and a templates of degree "
					+ "> 0, hence this method is incomplete.");
		}
		Collection<RankVar> rankVars = getRankVars();
		Collection<RankVar> siVars = getSIVars();
		m_template.init(this, !m_preferences.termination_check_nonlinear);
		s_Logger.debug("Variables for ranking functions: " + rankVars);
		s_Logger.debug("Variables for supporting invariants: " + siVars);
/*		// The following code makes examples like StemUnsat.bpl fail
		if (siVars.isEmpty()) {
			s_Logger.info("There is no variables for invariants; "
					+ "disabling supporting invariant generation.");
			m_preferences.num_strict_invariants = 0;
			m_preferences.num_non_strict_invariants = 0;
		} */
		if (m_stem == null) {
			s_Logger.info("There is no stem transition; "
					+ "disabling supporting invariant generation.");
			m_preferences.num_strict_invariants = 0;
			m_preferences.num_non_strict_invariants = 0;
		}
		
		// Assert all conjuncts generated from the template
		Collection<Term> constraints =
				buildConstraints(m_template, m_si_generators);
		m_num_motzkin = constraints.size();
		s_Logger.info("We have " + getNumMotzkin()
				+ " Motzkin's Theorem applications.");
		s_Logger.info("A total of " + getNumSIs()
				+ " supporting invariants were added.");
		for (Term constraint : constraints) {
			m_script.assertTerm(constraint);
		}
		
		// Check for a model
		LBool sat = m_script.checkSat();
		if (sat == LBool.SAT) {
			int pops = 0;
			if (m_preferences.simplify_result) {
				s_Logger.debug("Found a termination argument, trying to simplify.");
				pops = simplifyAssignment();
				s_Logger.debug("Setting " + pops + " variables to zero.");
			}
			s_Logger.debug("Extracting termination argument from model.");
			
			// Extract ranking function
			Map<Term, Rational> val_rf =
					getValuation(m_template.getVariables());
			m_ranking_function = m_template.extractRankingFunction(val_rf);
			
			// Extract supporting invariants
			for (SupportingInvariantGenerator sig : m_si_generators) {
				Map<Term, Rational> val_si = getValuation(sig.getVariables());
				m_supporting_invariants.add(sig.extractSupportingInvariant(
						val_si));
			}
			
			m_script.pop(pops);
		} else if (sat == LBool.UNKNOWN) {
			m_script.echo(new QuotedObject(SMTSolver.s_SolverUnknownMessage));
			// Problem: If we use the following line we can receive the 
			// following response which is not SMTLIB2 compliant.
			// (:reason-unknown canceled)
			// Object reason = m_script.getInfo(":reason-unknown");
			// TODO: discuss the above claim with Jürgen
		}
		return sat;
	}
	
	/**
	 * Tries to simplify a satisfying assignment by assigning zeros to
	 * variables. Gets stuck in local optima.
	 * 
	 * The procedure works according to this principle:
	 * <pre>
	 * random.shuffle(variables)
	 * for v in variables:
	 *     if sat with v = 0:
	 *         set v to 0
	 * </pre>
	 * 
	 * @return the number of pops required on m_script
	 */
	private int simplifyAssignment() {
		ArrayList<Term> variables = new ArrayList<Term>();
		
		// Add all variables form the ranking function and supporting invariants
		variables.addAll(m_template.getVariables());
		for (SupportingInvariantGenerator sig : m_si_generators) {
			variables.addAll(sig.getVariables());
		}
		
		// Shuffle the variable list for better effect
		Random rnd =  new Random(System.nanoTime());
		Collections.shuffle(variables, rnd);
		
		int pops = 0;
		for (int i = 0; i < variables.size(); ++i) {
			Term var = variables.get(i);
			m_script.push(1);
			m_script.assertTerm(m_script.term("=", var, m_script.numeral(BigInteger.ZERO)));
			if (m_script.checkSat() != LBool.SAT) {
				m_script.pop(1);
			} else {
				pops += 1;
			}
		}
		return pops;
	}
	
	/**
	 * @return the number of supporting invariants used
	 */
	public int getNumSIs() {
		assert m_si_generators != null;
		return m_si_generators.size();
	}
	
	/**
	 * @return the number of Motzkin's Theorem applications
	 */
	public int getNumMotzkin() {
		return m_num_motzkin;
	}
	
	/**
	 * @return the synthesized TerminationArgument
	 */
	public TerminationArgument getArgument() {
		assert synthesisSuccessful();
		return new TerminationArgument(m_ranking_function,
				m_supporting_invariants);
	}
}
