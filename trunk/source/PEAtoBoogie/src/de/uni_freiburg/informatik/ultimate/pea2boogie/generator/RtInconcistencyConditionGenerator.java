/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolExpressionTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RtInconcistencyConditionGenerator {

	private final ReqSymboltable mBoogieSymboltable;
	private final Term mPrimedInvariant;
	private final Script mScript;
	private final Term mTrue;
	private final Term mFalse;
	private final ManagedScript mManagedScript;
	private final Boogie2SMT mBoogie2Smt;
	private final Map<String, IProgramNonOldVar> mVars;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CddToSmt mCddToSmt;

	public RtInconcistencyConditionGenerator(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final ReqSymboltable symboltable,
			final Map<PatternType, PhaseEventAutomata> req2Automata, final BoogieDeclarations boogieDeclarations) {
		mBoogieSymboltable = symboltable;
		mServices = services;
		mLogger = logger;
		final SolverSettings settings = SolverBuilder.constructSolverSettings("", SolverMode.External_DefaultMode,
				false, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, false, null);
		mScript = SolverBuilder.buildAndInitializeSolver(services, storage, SolverMode.External_DefaultMode, settings,
				false, false, Logics.ALL.toString(), "RtInconsistencySolver");
		mManagedScript = new ManagedScript(services, mScript);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, false, services, false);
		mCddToSmt = new CddToSmt(services, storage, mScript, mBoogie2Smt,
				boogieDeclarations, mBoogieSymboltable);
		mVars = mBoogie2Smt.getBoogie2SmtSymbolTable().getGlobalsMap();
		mPrimedInvariant = constructPrimedStateInvariant(req2Automata);
	}

	public Expression nonDLCGenerator(final PhaseEventAutomata[] automata) {
		final int[][] phases = createPhasePairs(automata);

		final List<int[]> phasePermutations = CrossProducts.crossProduct(phases);
		final List<Term> rtInconsistencyChecks = new ArrayList<>();
		for (final int[] vector : phasePermutations) {
			assert vector.length == automata.length;
			final List<Term> outer = new ArrayList<>();
			final List<Term> impliesLHS = new ArrayList<>();
			for (int j = 0; j < vector.length; j++) {
				final PhaseEventAutomata automaton = automata[j];
				final int phaseIndex = vector[j];
				final String pcName = ReqSymboltable.getPcName(automaton);
				impliesLHS.add(genPCCompEQ(pcName, phaseIndex));
				final Phase phase = automaton.getPhases()[phaseIndex];
				final List<Term> inner = new ArrayList<>();
				for (final Transition trans : phase.getTransitions()) {
					inner.add(SmtUtils.and(mScript, genGuardANDPrimedStInv(trans), genStrictInv(trans)));
				}
				outer.add(SmtUtils.or(mScript, inner));
			}

			// first, compute rhs without primed invariant
			final Term checkPrimedRhs = SmtUtils.and(mScript, outer);
			final Term checkPrimedRhsAndPrimedInvariant = SmtUtils.and(mScript, checkPrimedRhs, mPrimedInvariant);
			final Term checkRhsAndInvariant = existentiallyProjectEventsAndPrimedVars(checkPrimedRhsAndPrimedInvariant);
			final Term checkRhsAndInvariantSimplified = simplify(checkRhsAndInvariant);
			if (checkRhsAndInvariantSimplified == mTrue) {
				continue;
			}

			final Term rtInconsistencyCheckLhs = SmtUtils.and(mScript, impliesLHS);
			final Term rtInconsistencyCheck =
					SmtUtils.implies(mScript, rtInconsistencyCheckLhs, checkRhsAndInvariantSimplified);

			rtInconsistencyChecks.add(rtInconsistencyCheck);
		}
		if (rtInconsistencyChecks.isEmpty()) {
			return null;
		}
		final Term finalCheck = SmtUtils.and(mScript, rtInconsistencyChecks);
		return mBoogie2Smt.getTerm2Expression().translate(finalCheck);
	}

	private Term simplify(final Term rtInconcistencyCheckRhsWithPrimes) {
		return SmtUtils.simplify(mManagedScript, rtInconcistencyCheckRhsWithPrimes, mServices,
				SimplificationTechnique.SIMPLIFY_DDA);
	}

	private Term constructPrimedStateInvariant(final Map<PatternType, PhaseEventAutomata> req2Automata) {

		final List<CDD> primedStateInvariants =
				req2Automata.entrySet().stream().filter(a -> a.getValue().getPhases().length == 1)
						.map(a -> a.getValue().getPhases()[0].getStateInvariant().prime()).collect(Collectors.toList());
		final Term result;
		if (primedStateInvariants.isEmpty()) {
			return mTrue;
		} else if (primedStateInvariants.size() == 1) {
			result = mCddToSmt.toSmt(primedStateInvariants.get(0));
		} else {
			final List<Term> terms = primedStateInvariants.stream().map(a -> mCddToSmt.toSmt(a)).collect(Collectors.toList());
			result = SmtUtils.and(mScript, terms);
		}
		return simplify(result);
	}

	private Term existentiallyProjectEventsAndPrimedVars(final Term term) {
		final Set<TermVariable> varsToRemove = getPrimedAndEventVars(term.getFreeVars());
		if (varsToRemove.isEmpty()) {
			return term;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Removing " + varsToRemove.size() + " variables");
		}
		final Term quantifiedFormula = SmtUtils.quantifier(mScript, QuantifiedFormula.EXISTS, varsToRemove, term);
		final Term quantifierFreeFormula =
				PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, quantifiedFormula,
						SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		return quantifierFreeFormula;
	}

	private Set<TermVariable> getPrimedAndEventVars(final TermVariable[] freeVars) {
		final Set<TermVariable> rtr = new HashSet<>();
		final Set<String> primedVars = mBoogieSymboltable.getPrimedVars();
		final Set<String> eventVars = mBoogieSymboltable.getEventVars();
		for (final TermVariable var : freeVars) {
			final Expression expr = mBoogie2Smt.getTerm2Expression().translate(var);
			if (expr instanceof IdentifierExpression) {
				final String name = ((IdentifierExpression) expr).getIdentifier();
				if (primedVars.contains(name) || eventVars.contains(name)) {
					rtr.add(var);
				}
			} else {
				throw new AssertionError();
			}
		}

		return rtr;
	}

	private static int[][] createPhasePairs(final PhaseEventAutomata[] automata) {
		final int[][] phases = new int[automata.length][];
		for (int i = 0; i < automata.length; i++) {
			final PhaseEventAutomata automaton = automata[i];
			final int phaseCount = automaton.getPhases().length;
			phases[i] = new int[phaseCount];
			for (int j = 0; j < phaseCount; j++) {
				phases[i][j] = j;
			}
		}
		return phases;
	}

	private Term genStrictInv(final Transition transition) {
		final Phase phase = transition.getDest();
		final String[] resetVars = transition.getResets();
		final List<String> resetList = Arrays.asList(resetVars);
		return mCddToSmt.toSmt(new StrictInvariant().genStrictInv(phase.getClockInvariant(), resetList));
	}

	private Term genGuardANDPrimedStInv(final Transition transition) {
		final Term guard = mCddToSmt.toSmt(transition.getGuard());
		final Phase phase = transition.getDest();
		final Term primedStInv = mCddToSmt.toSmt(phase.getStateInvariant().prime());
		return SmtUtils.and(mScript, guard, primedStInv);
	}

	private Term genPCCompEQ(final String pcName, final int phaseIndex) {
		return SmtUtils.binaryEquality(mScript, mCddToSmt.getTermVarTerm(pcName), mScript.numeral(Integer.toString(phaseIndex)));
	}



}
