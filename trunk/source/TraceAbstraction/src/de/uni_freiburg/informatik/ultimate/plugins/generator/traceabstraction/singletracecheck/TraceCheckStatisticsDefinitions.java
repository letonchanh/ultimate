/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;

public enum TraceCheckStatisticsDefinitions implements IStatisticsElement {

	SsaConstructionTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	SatisfiabilityAnalysisTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	InterpolantComputationTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),

	NumberOfCodeBlocks(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	NumberOfCodeBlocksAsserted(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	NumberOfCheckSat(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	ConstructedInterpolants(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	QuantifiedInterpolants(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	SizeOfPredicates(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sDataBeforeKey),

	NumberOfNonLiveVariables(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	ConjunctsInSsa(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	ConjunctsInUnsatCore(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	InterpolantComputations(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	PerfectInterpolantSequences(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sDataBeforeKey),

	InterpolantCoveringCapability(BackwardCoveringInformation.class, CoverageAnalysis.DEFAULT_AGGREGATION,
			AStatisticsType.sDataBeforeKey),;

	private final Class<?> mClazz;
	private final Function<Object, Function<Object, Object>> mAggr;
	private final Function<String, Function<Object, String>> mPrettyprinter;

	TraceCheckStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
			final Function<String, Function<Object, String>> prettyprinter) {
		mClazz = clazz;
		mAggr = aggr;
		mPrettyprinter = prettyprinter;
	}

	@Override
	public Object aggregate(final Object o1, final Object o2) {
		return mAggr.apply(o1).apply(o2);
	}

	@Override
	public String prettyprint(final Object o) {
		return mPrettyprinter.apply(name()).apply(o);
	}

	@Override
	public Class<?> getDataType() {
		return mClazz;
	}
}