/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Provides static methods for handling of quantifiers and their finite connectives
 * (and/or)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierUtils {
	
	private QuantifierUtils() {
		// do not instantiate
	}

	/**
	 * Compose term with outer operation of a XNF. For the case of existential quantification: Compose disjuncts to a
	 * disjunction.
	 */
	public static Term applyCorrespondingFiniteConnective(final Script script, final int quantifier,
			final Collection<Term> xjunctsOuter) {
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.or(script, xjunctsOuter);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.and(script, xjunctsOuter);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return result;
	}

	public static Term applyCorrespondingFiniteConnective(final Script script, final int quantifier,
			final Term[] xjunctsOuter) {
		return applyCorrespondingFiniteConnective(script, quantifier, Arrays.asList(xjunctsOuter));
	}

	/**
	 * Compose term with inner operation of a XNF. For the case of existential quantification: Compose atoms to a
	 * conjunction.
	 */
	public static Term applyDualFiniteConnective(final Script script, final int quantifier,
			final Collection<Term> xjunctsInner) {
		final Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.and(script, xjunctsInner);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.or(script, xjunctsInner);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return result;
	}

	public static Term applyDualFiniteConnective(final Script script, final int quantifier,
			final Term... xjunctsInner) {
		return applyDualFiniteConnective(script, quantifier, Arrays.asList(xjunctsInner));
	}

	/**
	 * Apply equals if quantifier is existential and not equals if quantifier is universal.
	 */
	public static Term applyDerOperator(final Script script, final int quantifier, final Term lhs, final Term rhs) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.binaryEquality(script, lhs, rhs);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.distinct(script, lhs, rhs);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return result;
	}

	/**
	 * Apply not equals if quantifier is existential and equals if quantifier is universal.
	 */
	public static Term applyAntiDerOperator(final Script script, final int quantifier, final Term lhs, final Term rhs) {
		Term result;
		if (quantifier == QuantifiedFormula.EXISTS) {
			result = SmtUtils.distinct(script, lhs, rhs);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			result = SmtUtils.binaryEquality(script, lhs, rhs);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return result;
	}

	/**
	 * Get all parameters of the outer operation of a XNF For the case of existential quantification: Get all disjuncts
	 * of a formula in DNF. (conjuncts of CNF for case of universal quantification)
	 */
	public static Term[] getXjunctsOuter(final int quantifier, final Term xnf) {
		Term[] xjunctsOuter;
		if (quantifier == QuantifiedFormula.EXISTS) {
			xjunctsOuter = SmtUtils.getDisjuncts(xnf);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			xjunctsOuter = SmtUtils.getConjuncts(xnf);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return xjunctsOuter;
	}

	/**
	 * Get all parameters of the inner operation of a XNF For the case of existential quantification: Get all conjuncts
	 * of a conjunction. (disjuncts of disjunction in case of universal quantification)
	 */
	public static Term[] getXjunctsInner(final int quantifier, final Term xnf) {
		Term[] xjunctsOuter;
		if (quantifier == QuantifiedFormula.EXISTS) {
			xjunctsOuter = SmtUtils.getConjuncts(xnf);
		} else if (quantifier == QuantifiedFormula.FORALL) {
			xjunctsOuter = SmtUtils.getDisjuncts(xnf);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		return xjunctsOuter;
	}
	
	
	public static Term getNeutralElement(final Script script, final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return script.term("false");
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return script.term("true");
		} else {
			throw new AssertionError("unknown quantifier");
		}
	}
	
	public static Term getAbsorbingElement(final Script script, final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return script.term("true");
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return script.term("false");
		} else {
			throw new AssertionError("unknown quantifier");
		}
	}

	
	
}