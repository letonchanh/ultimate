/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.AffineRelation.TransformInequality;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

/**
 * Brings Terms into a normal form where all parameters that of commutative functions (resp. functions for that this
 * class knows that they are commutative) are sorted according to their hash code. Furthermore all AffineRelations are
 * transformed into positive normal form.
 *
 * This can simplify terms, e.g., (or (and A B) (and B A)) will be simplified to (and A B) (except in the very rare case
 * where the hash code of A and B coincides).
 *
 * Note that this is still experimental. Problems: AffineRelations are not yet sorted according to hash code. We do not
 * want this, because it is a problem for legibility, we do not want to have terms like (+ x*2 1 3*y), instead we would
 * prefer (+ 2*x 3*y 1): coefficient before variable, constant term at last position.
 *
 * @author Matthias Heizmann
 *
 */
public class CommuhashNormalForm {

	private static final boolean DEBUG_LOG_SIZES = false;
	private final IUltimateServiceProvider mServices;
	private final Script mScript;

	public CommuhashNormalForm(final IUltimateServiceProvider services, final Script script) {
		super();
		mServices = services;
		mScript = script;
	}

	public Term transform(final Term term) {
		final ILogger logger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		if (DEBUG_LOG_SIZES) {
			logger.debug(new DebugMessage("applying CommuhashNormalForm to formula of DAG size {0}",
					new DagSizePrinter(term)));
		}
		final Term result = (new CommuhashNormalFormHelper()).transform(term);
		if (DEBUG_LOG_SIZES) {
			logger.debug(
					new DebugMessage("DAG size before CommuhashNormalForm {0}, DAG size after CommuhashNormalForm {1}",
							new DagSizePrinter(term), new DagSizePrinter(result)));
		}
		assert (Util.checkSat(mScript,
				mScript.term("distinct", term, result)) != LBool.SAT) : "CommuhashNormalForm transformation unsound";
		return result;
	}

	private class CommuhashNormalFormHelper extends TermTransformer {

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final String funcname = appTerm.getFunction().getApplicationString();
			if (CommuhashUtils.isKnownToBeCommutative(funcname)) {
				final Term simplified = constructlocallySimplifiedTermWithSortedParams(funcname,
						appTerm.getSort().getIndices(), newArgs);
				setResult(simplified);
			} else {
				super.convertApplicationTerm(appTerm, newArgs);
			}
		}

		@Override
		protected void convert(final Term term) {
			try {
				final Term result = tryToTransformToPositiveNormalForm(term);
				setResult(result);
			} catch (final NotAffineException e) {
				// descent, input is no AffineRelation
				super.convert(term);
			}
		}

		private Term tryToTransformToPositiveNormalForm(final Term simplified) throws NotAffineException {
			final AffineRelation affRel = new AffineRelation(mScript, simplified, TransformInequality.NO_TRANFORMATION);
			final Term pnf = affRel.positiveNormalForm(mScript);
			return pnf;
		}

		private Term constructlocallySimplifiedTermWithSortedParams(final String funcname, final BigInteger[] indices,
				final Term[] params) {
			final Term[] sortedParams = CommuhashUtils.sortByHashCode(params);
			final Term simplified = SmtUtils.termWithLocalSimplification(mScript, funcname, indices, sortedParams);
			return simplified;
		}

		@Override
		public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
			final Term result = SmtUtils.quantifier(mScript, old.getQuantifier(),
					new HashSet<>(Arrays.asList(old.getVariables())), newBody);
			setResult(result);
		}

	}
}
