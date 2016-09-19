/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.summarycomputationgraph;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.PriorityComparator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game.IGameState;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.CanonicalParitalComparatorForMaps;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;

/**
 * Node in the graph that we build for computation of summaries.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class WeightedSummaryTargets {
	
	private final Map<IGameState, Integer> mTarget2Priority;
	
	
	public WeightedSummaryTargets(final Map<IGameState, Integer> target2Priority) {
		super();
		mTarget2Priority = target2Priority;
	}



	public WeightedSummaryTargets computeUpdate(final int priority) {
		switch (priority) {
		case 2:
			return this;
		case 1:
		case 0: {
			final Map<IGameState, Integer> newMap = new HashMap<IGameState, Integer>();
			for (final Entry<IGameState, Integer> entry : mTarget2Priority.entrySet()) {
				newMap.put(entry.getKey(), Math.min(priority, entry.getValue()));
			}
			return new WeightedSummaryTargets(newMap);
		}
		default:
			throw new IllegalArgumentException("unsupported value " + priority);
		}
	}




	public static class WeightedSummaryTargetsComparator implements IPartialComparator<WeightedSummaryTargets> {

		@Override
		public ComparisonResult compare(final WeightedSummaryTargets o1, final WeightedSummaryTargets o2) {
			return new CanonicalParitalComparatorForMaps<IGameState, Integer>(
					new PriorityComparator()).compare(o1.mTarget2Priority, o2.mTarget2Priority);
		}
		
	}
	
	
	
	
}
