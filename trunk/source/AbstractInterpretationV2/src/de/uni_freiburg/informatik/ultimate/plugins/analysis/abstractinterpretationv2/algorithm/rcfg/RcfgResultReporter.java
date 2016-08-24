/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractCounterexample;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RcfgResultReporter<STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, VARDECL>
		implements IResultReporter<STATE, CodeBlock, VARDECL, ProgramPoint> {

	protected final IUltimateServiceProvider mServices;

	public RcfgResultReporter(final IUltimateServiceProvider services) {
		mServices = services;
	}

	@Override
	public void reportPossibleError(final AbstractCounterexample<STATE, CodeBlock, ?, ProgramPoint> cex) {
		final Map<Integer, ProgramState<Term>> programStates = new HashMap<>();
		final List<RCFGEdge> trace = new ArrayList<>();

		programStates.put(-1, computeProgramState(cex.getInitialState()));

		int i = 0;
		for (final Triple<STATE, ProgramPoint, CodeBlock> elem : cex.getAbstractExecution()) {
			trace.add(elem.getThird());
			programStates.put(i, computeProgramState(elem.getFirst()));
			++i;
		}
		final RcfgProgramExecution pex = new RcfgProgramExecution(trace, programStates);

		final IResult result =
				new UnprovableResult<ProgramPoint, RCFGEdge, Term>(Activator.PLUGIN_ID, getLast(cex),
						mServices.getBacktranslationService(), pex, "abstract domain could reach this error location");

		mServices.getResultService().reportResult(Activator.PLUGIN_ID, result);
	}

	private ProgramState<Term> computeProgramState(final STATE state) {
		// TODO: Compute program state
		return new ProgramState<>(Collections.emptyMap());
	}

	private ProgramPoint getLast(final AbstractCounterexample<STATE, CodeBlock, ?, ProgramPoint> cex) {
		final int size = cex.getAbstractExecution().size();
		return cex.getAbstractExecution().get(size - 1).getSecond();
	}

	@Override
	public void reportSafe(final CodeBlock first) {
		reportSafe(first, "No error locations were reached.");
	}

	@Override
	public void reportSafe(final CodeBlock first, final String msg) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new AllSpecificationsHoldResult(Activator.PLUGIN_NAME, msg));
	}

}
