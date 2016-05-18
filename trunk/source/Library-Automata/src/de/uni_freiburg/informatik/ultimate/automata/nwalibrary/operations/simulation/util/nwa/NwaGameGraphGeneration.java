/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.fair.FairGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ECountingMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.ETimeMeasure;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.performance.SimulationPerformance;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UniqueQueue;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.relation.Hep;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.relation.Quin;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Generates game graphs based on nwa automaton. Supports different types of
 * simulation types.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class NwaGameGraphGeneration<LETTER, STATE> {
	/**
	 * Data structure that allows a fast access to {@link DuplicatorVertex}
	 * objects by using their representation:<br/>
	 * <b>(State of spoiler or q0, Letter spoiler used before, State of
	 * duplicator or q1, bit, type of transition, summarize edge, sink)</b>.
	 */
	private final HashMap<Hep<STATE, STATE, LETTER, Boolean, ETransitionType, SummarizeEdge<LETTER, STATE>, DuplicatorWinningSink<LETTER, STATE>>, DuplicatorVertex<LETTER, STATE>> m_AutomatonStatesToGraphDuplicatorVertex;
	/**
	 * Data structure that allows a fast access to {@link SpoilerVertex} objects
	 * by using their representation:<br/>
	 * <b>(State of spoiler or q0, State of duplicator or q1, bit)</b>.
	 */
	private final HashMap<Quin<STATE, STATE, Boolean, SummarizeEdge<LETTER, STATE>, DuplicatorWinningSink<LETTER, STATE>>, SpoilerVertex<LETTER, STATE>> m_AutomatonStatesToGraphSpoilerVertex;
	/**
	 * State symbol that stands for an empty stack.
	 */
	private final STATE m_Bottom;
	/**
	 * Set that contains vertices where both states have bottom as possible down
	 * state. This are, for example, initial states of the automaton or states
	 * that can be reached from initial states, using internal transitions.
	 */
	private final HashSet<Vertex<LETTER, STATE>> m_BottomVertices;
	/**
	 * Data structure of all duplicator vertices that use an outgoing return
	 * transition. They are used for summarize edge generation.
	 */
	private final HashSet<DuplicatorDoubleDeckerVertex<LETTER, STATE>> m_DuplicatorReturningVertices;
	/**
	 * Map of all duplicator winning sinks of the graph. Provides a fast access
	 * via the sink entry.
	 */
	private final HashMap<SpoilerDoubleDeckerVertex<LETTER, STATE>, DuplicatorWinningSink<LETTER, STATE>> m_EntryToSink;
	/**
	 * Game graph to generate a nwa graph for it.
	 */
	private final AGameGraph<LETTER, STATE> m_GameGraph;
	/**
	 * ILogger of the Ultimate framework.
	 */
	private final ILogger m_Logger;
	/**
	 * The underlying nwa automaton, as double decker automaton, from which the
	 * game graph gets generated.
	 */
	private final IDoubleDeckerAutomaton<LETTER, STATE> m_Nwa;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer m_ProgressTimer;
	/**
	 * Amount of states the result automaton has.
	 */
	private int m_ResultAmountOfStates;
	/**
	 * Amount of transitions the result automaton has.
	 */
	private int m_ResultAmountOfTransitions;
	/**
	 * Data structure of all omitted predecessors of return invoker vertices.
	 * Those are predecessors that are directly loosing for duplicator in the
	 * direct simulation game. Return invoker are duplicator vertices that use a
	 * return transition and by that possibly invoke the creation of summarize
	 * edges.
	 */
	private final HashMap<Vertex<LETTER, STATE>, List<Vertex<LETTER, STATE>>> m_ReturnInvokerOmittedPredecessors;
	/**
	 * Data structure of all omitted successors of return invoker vertices.
	 * Those are successors that are directly loosing for duplicator in the
	 * direct simulation game. Return invoker are duplicator vertices that use a
	 * return transition and by that possibly invoke the creation of summarize
	 * edges.
	 */
	private final HashMap<Vertex<LETTER, STATE>, List<Vertex<LETTER, STATE>>> m_ReturnInvokerOmittedSuccessors;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;
	/**
	 * Performance logging for this object.
	 */
	private final SimulationPerformance m_SimulationPerformance;
	/**
	 * Type of the simulation to use.
	 */
	private final ESimulationType m_SimulationType;
	/**
	 * Map of all summarize edges of the graph. Provides a fast access via
	 * source and destination of the edge.
	 */
	private final NestedMap2<SpoilerDoubleDeckerVertex<LETTER, STATE>, SpoilerDoubleDeckerVertex<LETTER, STATE>, SummarizeEdge<LETTER, STATE>> m_SrcDestToSummarizeEdges;

	/**
	 * Creates a new generation object that modifies a given graph using a given
	 * nwa automaton and a desired simulation method.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param progressTimer
	 *            Timer used for responding to timeouts and operation
	 *            cancellation.
	 * @param logger
	 *            ILogger of the Ultimate framework.
	 * @param nwa
	 *            The underlying nwa automaton from which the game graph gets
	 *            generated.
	 * @param gameGraph
	 *            Game graph that should get modified by this object
	 * @param simulationType
	 *            Simulation method to use for graph generation. Supported types
	 *            are {@link ESimulationType#DIRECT DIRECT} and
	 *            {@link ESimulationType#FAIR FAIR}.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public NwaGameGraphGeneration(final AutomataLibraryServices services, final IProgressAwareTimer progressTimer,
			final ILogger logger, final IDoubleDeckerAutomaton<LETTER, STATE> nwa,
			final AGameGraph<LETTER, STATE> gameGraph, final ESimulationType simulationType)
					throws AutomataOperationCanceledException {
		m_Services = services;
		m_Nwa = nwa;
		m_AutomatonStatesToGraphDuplicatorVertex = new HashMap<>();
		m_AutomatonStatesToGraphSpoilerVertex = new HashMap<>();
		m_DuplicatorReturningVertices = new HashSet<>();
		m_SrcDestToSummarizeEdges = new NestedMap2<>();
		m_ReturnInvokerOmittedSuccessors = new HashMap<>();
		m_ReturnInvokerOmittedPredecessors = new HashMap<>();
		m_EntryToSink = new HashMap<>();
		m_BottomVertices = new HashSet<>();
		m_Bottom = m_Nwa.getEmptyStackState();
		m_Logger = logger;
		m_ProgressTimer = progressTimer;
		m_GameGraph = gameGraph;
		m_SimulationType = simulationType;

		m_ResultAmountOfStates = 0;
		m_ResultAmountOfTransitions = 0;
		m_SimulationPerformance = new SimulationPerformance(simulationType, false);
	}

	/**
	 * Clears all internal data structures of this object.
	 */
	public void clear() {
		m_BottomVertices.clear();
		m_DuplicatorReturningVertices.clear();
		m_EntryToSink.clear();
		m_SrcDestToSummarizeEdges.clear();
		m_ReturnInvokerOmittedSuccessors.clear();
		m_ReturnInvokerOmittedPredecessors.clear();
	}

	/**
	 * Computes which vertex down states are safe and marks them so. It does so
	 * by using a search starting at vertices which can have a down state
	 * configuration of [bottom, bottom].
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void computeSafeVertexDownStates() throws AutomataOperationCanceledException {
		m_Logger.debug("Computing which vertex down states are safe.");
		// Add roots of search to the queue
		Queue<SearchElement<LETTER, STATE>> searchQueue = new LinkedList<SearchElement<LETTER, STATE>>();
		for (Vertex<LETTER, STATE> rootVertex : m_BottomVertices) {
			if (!(rootVertex instanceof IHasVertexDownStates<?>)) {
				continue;
			}
			@SuppressWarnings("unchecked")
			IHasVertexDownStates<STATE> rootVertexWithDownStates = (IHasVertexDownStates<STATE>) rootVertex;
			VertexDownState<STATE> rootVertexDownState = new VertexDownState<STATE>(m_Bottom, m_Bottom);
			if (!rootVertexWithDownStates.hasVertexDownState(rootVertexDownState)) {
				// Confirm that the root vertex has the desired configuration
				// [bottom, bottom].
				continue;
			}
			searchQueue.add(new SearchElement<>(rootVertex, rootVertexDownState));
		}

		// Process queue
		while (!searchQueue.isEmpty()) {
			SearchElement<LETTER, STATE> searchElement = searchQueue.poll();
			Vertex<LETTER, STATE> searchVertex = searchElement.getVertex();
			VertexDownState<STATE> searchDownState = searchElement.getDownState();

			if (!(searchVertex instanceof IHasVertexDownStates<?>)) {
				continue;
			}
			@SuppressWarnings("unchecked")
			IHasVertexDownStates<STATE> searchVertexWithDownStates = (IHasVertexDownStates<STATE>) searchVertex;
			// If element was already processed, abort this search path
			if (searchVertexWithDownStates.isVertexDownStateSafe(searchDownState)) {
				continue;
			}
			// Mark current down state as safe
			searchVertexWithDownStates.setVertexDownStateSafe(searchDownState, true);
			m_Logger.debug("\tMarked down state as safe: " + searchElement);

			// Add successors with their corresponding safe down states
			Set<Vertex<LETTER, STATE>> successors = m_GameGraph.getSuccessors(searchVertex);
			if (successors == null) {
				continue;
			}
			for (Vertex<LETTER, STATE> succ : successors) {
				if (succ instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
					// Successor is duplicator
					DuplicatorDoubleDeckerVertex<LETTER, STATE> succAsDuplicatorDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) succ;
					ETransitionType transType = succAsDuplicatorDD.getTransitionType();
					// We do not need to account for other types as the graph is
					// unmodified at this point
					if (transType.equals(ETransitionType.CALL)) {
						// Left down state changes by using
						// 'spoiler -call-> duplicator'
						VertexDownState<STATE> downState = new VertexDownState<STATE>(searchVertex.getQ0(),
								searchDownState.getRightDownState());
						if (succAsDuplicatorDD.hasVertexDownState(downState)) {
							searchQueue.add(new SearchElement<>(succAsDuplicatorDD, downState));
						}
					} else if (transType.equals(ETransitionType.RETURN)) {
						// Left down state changes by using
						// 'spoiler -return-> duplicator'
						VertexDownState<STATE> downStateEmpty = new VertexDownState<STATE>(m_Bottom,
								searchDownState.getRightDownState());
						// Only use the edge if left state was not already
						// bottom, else return is not possible.
						if (!searchDownState.getLeftDownState().equals(m_Bottom)
								&& succAsDuplicatorDD.hasVertexDownState(downStateEmpty)
								&& succAsDuplicatorDD.hasVertexDownState(searchDownState)) {
							// TODO Somehow we need to know all possible down
							// states that can possibly lie under the left down
							// state. They are a subset of all possible
							// down states for that state. It is wrong to only
							// assume the same left down state is there again.
							// TODO Ensure that unbalanced stack levels of left
							// and right down states are not possible, i.e. [q0,
							// bottom] is not possible for the duplicator
							// successor here.
							searchQueue.add(new SearchElement<>(succAsDuplicatorDD, downStateEmpty));
							searchQueue.add(new SearchElement<>(succAsDuplicatorDD, searchDownState));
						}
					} else {
						if (succAsDuplicatorDD.hasVertexDownState(searchDownState)) {
							searchQueue.add(new SearchElement<>(succAsDuplicatorDD, searchDownState));
						}
					}
				} else {
					// Current vertex is duplicator
					DuplicatorDoubleDeckerVertex<LETTER, STATE> searchVertexAsDuplicatorDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) searchVertex;
					SpoilerDoubleDeckerVertex<LETTER, STATE> succAsSpoilerDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) succ;
					ETransitionType transType = searchVertexAsDuplicatorDD.getTransitionType();
					// We do not need to account for other types as the graph is
					// unmodified at this point
					if (transType.equals(ETransitionType.CALL)) {
						// Right down state changes by using
						// 'duplicator -call-> spoiler'
						VertexDownState<STATE> downState = new VertexDownState<STATE>(
								searchDownState.getLeftDownState(), searchVertex.getQ1());
						if (succAsSpoilerDD.hasVertexDownState(downState)) {
							searchQueue.add(new SearchElement<>(succAsSpoilerDD, downState));
						}
					} else if (transType.equals(ETransitionType.RETURN)) {
						// Right down state changes by using
						// 'duplicator -return-> spoiler'
						VertexDownState<STATE> downStateEmpty = new VertexDownState<STATE>(
								searchDownState.getRightDownState(), m_Bottom);
						// Only use the edge if right state was not already
						// bottom, else return is not possible.
						if (!searchDownState.getRightDownState().equals(m_Bottom)
								&& succAsSpoilerDD.hasVertexDownState(downStateEmpty)
								&& succAsSpoilerDD.hasVertexDownState(searchDownState)) {
							// TODO Somehow we need to know all possible down
							// states that can possibly lie under the right down
							// state. They are a subset of all possible
							// down states for that state. It is wrong to only
							// assume the same right down state is there again.
							// TODO Ensure that unbalanced stack levels of left
							// and right down states are not possible, i.e.
							// [bottom, q0] or [q0, bottom] is not possible
							// for the spoiler successor here.
							searchQueue.add(new SearchElement<>(succAsSpoilerDD, downStateEmpty));
							searchQueue.add(new SearchElement<>(succAsSpoilerDD, searchDownState));
						}
					} else {
						if (succAsSpoilerDD.hasVertexDownState(searchDownState)) {
							searchQueue.add(new SearchElement<>(succAsSpoilerDD, searchDownState));
						}
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
					m_Logger.debug("Stopped in computeSafeVertexDownStates/successors");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}
		m_BottomVertices.clear();
	}

	/**
	 * Computes the priorities of all previous generated summarize edges.
	 * 
	 * @throws IllegalStateException
	 *             If computing summarize edge priorities could not be done
	 *             because a live lock occurred.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void computeSummarizeEdgePriorities() throws AutomataOperationCanceledException {
		m_Logger.debug("Computing priorities of summarize edges.");
		Queue<SearchElement<LETTER, STATE>> searchQueue = new UniqueQueue<>();
		HashMap<Pair<Vertex<LETTER, STATE>, VertexDownState<STATE>>, Integer> searchPriorities = new HashMap<>();
		LoopDetector<LETTER, STATE> loopDetector = new LoopDetector<>(m_GameGraph, m_Logger, m_ProgressTimer);
		HashMap<Pair<Vertex<LETTER, STATE>, VertexDownState<STATE>>, SummarizeEdge<LETTER, STATE>> invokerToSummarizeEdge = new HashMap<>();

		// Every vertex can maximal be added '3 * out-degree' times to the queue
		// TODO Performance impact of BigInteger is to high for a safety check.
		// This event may not even be possible for correct game graphs. In this
		// case, remove it after verification.
		BigInteger maxAmountOfSearches = BigInteger.valueOf(m_GameGraph.getSize()).pow(2)
				.multiply(BigInteger.valueOf(3));
		BigInteger searchCounter = BigInteger.ZERO;

		// Add starting elements
		for (Triple<SpoilerDoubleDeckerVertex<LETTER, STATE>, SpoilerDoubleDeckerVertex<LETTER, STATE>, SummarizeEdge<LETTER, STATE>> summarizeEdgeEntry : m_SrcDestToSummarizeEdges
				.entrySet()) {
			SummarizeEdge<LETTER, STATE> summarizeEdge = summarizeEdgeEntry.getThird();

			// In direct simulation every edge will have a priority of zero,
			// since every vertex has a priority of zero.
			if (m_SimulationType == ESimulationType.DIRECT) {
				// Do not add something to the queue and finish
				// the method by that
				summarizeEdge.setPriority(0);
			} else {
				Vertex<LETTER, STATE> spoilerInvoker = summarizeEdge.getSpoilerInvoker();
				Vertex<LETTER, STATE> edgeSource = summarizeEdge.getSource();
				VertexDownState<STATE> invokingState = new VertexDownState<>(edgeSource.getQ0(), edgeSource.getQ1());

				SearchElement<LETTER, STATE> searchElement = new SearchElement<LETTER, STATE>(spoilerInvoker,
						invokingState, null, summarizeEdge);
				searchQueue.add(searchElement);

				// Memorize invoker element for detection of
				// corresponding summarize edges
				invokerToSummarizeEdge.put(new Pair<>(spoilerInvoker, invokingState), summarizeEdge);
			}
		}

		// Start the search
		while (!searchQueue.isEmpty() && searchCounter.compareTo(maxAmountOfSearches) <= 0) {
			searchCounter.add(BigInteger.ONE);
			SearchElement<LETTER, STATE> searchElement = searchQueue.poll();
			Vertex<LETTER, STATE> searchVertex = searchElement.getVertex();
			VertexDownState<STATE> searchDownState = searchElement.getDownState();
			SummarizeEdge<LETTER, STATE> searchSummarizeEdge = searchElement.getSummarizeEdge();

			if (searchVertex instanceof IHasVertexDownStates) {
				@SuppressWarnings("unchecked")
				IHasVertexDownStates<STATE> searchVertexWithDownStates = (IHasVertexDownStates<STATE>) searchVertex;
				if (!searchVertexWithDownStates.isVertexDownStateSafe(searchDownState)) {
					// TODO Do something with that information
					m_Logger.debug("\t\tDownstate is marked unsafe: " + searchElement);
				}
			}

			boolean isSearchVertexDuplicatorDD = false;
			DuplicatorDoubleDeckerVertex<LETTER, STATE> searchVertexAsDuplicatorDD = null;
			if (searchVertex instanceof DuplicatorDoubleDeckerVertex) {
				searchVertexAsDuplicatorDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) searchVertex;
				isSearchVertexDuplicatorDD = true;
			}

			// Calculate search priority of element by using the priorities of
			// successors
			int optimalSuccPriority = SummarizeEdge.NO_PRIORITY;
			int optimalNonLoopSuccPriority = SummarizeEdge.NO_PRIORITY;
			int optimalLoopSuccPriority = SummarizeEdge.NO_PRIORITY;
			boolean isSpoiler = searchVertex.isSpoilerVertex();
			int optimalValue;
			int worstValue;
			if (isSpoiler) {
				optimalValue = 1;
				worstValue = 0;
			} else {
				optimalValue = 0;
				worstValue = 1;
			}
			// We first use priorities of non-loop successors. If the computed
			// search priority is not the worst value, we also take loop
			// successors into account.
			Set<Vertex<LETTER, STATE>> successors = m_GameGraph.getSuccessors(searchVertex);
			if (successors != null) {
				for (Vertex<LETTER, STATE> succ : successors) {
					int succPriority = SummarizeEdge.NO_PRIORITY;

					// Reject successor if it is null
					if (succ == null) {
						continue;
					}
					if (succ instanceof DuplicatorDoubleDeckerVertex) {
						// Successor is duplicator vertex
						DuplicatorDoubleDeckerVertex<LETTER, STATE> succAsDuplicatorDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) succ;
						ETransitionType transitionType = succAsDuplicatorDD.getTransitionType();

						// We will reject successor if it has no search priority
						// yet. This may indicate that the successor is
						// not capable of reaching the destination of
						// the summarize edge, which priority currently
						// shall be computed. If it, however, is capable
						// of that, he may force an update on the
						// current vertex later anyway. At this time the
						// successor will also have a search priority.

						if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
								|| transitionType == ETransitionType.SUMMARIZE_EXIT) {
							// Ignore return and special edges
							continue;
						} else if (transitionType == ETransitionType.SUMMARIZE_ENTRY) {
							// Use min(summarizeEdgePriority,
							// summarizeEdgeDestinationPriority) as priority
							// candidate
							SummarizeEdge<LETTER, STATE> summarizeEdge = succAsDuplicatorDD.getSummarizeEdge();
							Vertex<LETTER, STATE> destination = summarizeEdge.getDestination();
							int summarizeEdgePriority = summarizeEdge.getPriority();

							if (destination instanceof IHasVertexDownStates<?>) {
								@SuppressWarnings("unchecked")
								IHasVertexDownStates<STATE> destinationWithDownStates = (IHasVertexDownStates<STATE>) destination;
								if (!destinationWithDownStates.hasVertexDownState(searchDownState)) {
									// Reject successor if there is no
									// corresponding down state.
									// This should not be possible on correctly
									// generated game graphs though.
									continue;
								}
							}

							if (summarizeEdgePriority == SummarizeEdge.NO_PRIORITY) {
								// If summarize edge has no priority yet, use
								// the neutral element 2.
								summarizeEdgePriority = 2;
							}

							Integer destinationSearchPriority = searchPriorities
									.get(new Pair<>(destination, searchDownState));
							if (destinationSearchPriority == null
									|| destinationSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = Math.min(summarizeEdgePriority, destinationSearchPriority);
							// Change successor to destination. This
							// represents following the summarize edge instead
							// of using the fake vertices, which are used to
							// model the summarize edge.
							succ = destination;
						} else if (transitionType == ETransitionType.CALL) {
							// Left down state changes by using
							// 'spoiler -call-> duplicator'
							VertexDownState<STATE> downState = new VertexDownState<>(searchVertex.getQ0(),
									searchDownState.getRightDownState());
							Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, downState));
							if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = succSearchPriority;
						} else {
							Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, searchDownState));
							if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
								continue;
							}
							succPriority = succSearchPriority;
						}
					} else {
						// Successor is spoiler vertex
						if (isSearchVertexDuplicatorDD) {
							ETransitionType transitionType = searchVertexAsDuplicatorDD.getTransitionType();
							if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
									|| transitionType == ETransitionType.SUMMARIZE_ENTRY
									|| transitionType == ETransitionType.SUMMARIZE_EXIT) {
								// Ignore return and special edges
								break;
							} else if (transitionType == ETransitionType.CALL) {
								// Right down state changes by using
								// 'duplicator -call-> spoiler'
								VertexDownState<STATE> downState = new VertexDownState<>(
										searchDownState.getLeftDownState(), searchVertex.getQ1());
								Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, downState));
								if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
									continue;
								}
								succPriority = succSearchPriority;
							} else {
								Integer succSearchPriority = searchPriorities.get(new Pair<>(succ, searchDownState));
								if (succSearchPriority == null || succSearchPriority == SummarizeEdge.NO_PRIORITY) {
									continue;
								}
								succPriority = succSearchPriority;
							}
						}
					}
					// Evaluate the priority of the current successor
					// Differentiate between non-loop and loop vertices
					if (!loopDetector.isLoopVertex(succ, searchSummarizeEdge.getSpoilerInvoker(), searchVertex)) {
						// TODO Improve efficiency of isLoopVertex computation
						// Search for the optimal value under all successors.
						// If that is not present try to increase to 2 until
						// optimal value is reached.
						if (optimalNonLoopSuccPriority != optimalValue) {
							if (succPriority > optimalNonLoopSuccPriority) {
								optimalNonLoopSuccPriority = succPriority;
							}
							if (succPriority == optimalValue) {
								optimalNonLoopSuccPriority = succPriority;
								// Break since the optimal value is found, it
								// can
								// not get better anymore.
								break;
							}
						}
					} else {
						m_Logger.debug("\t\tSuccessor is loop vertex: " + succ);
						if (optimalLoopSuccPriority != optimalValue) {
							if (succPriority > optimalLoopSuccPriority) {
								optimalLoopSuccPriority = succPriority;
							}
							if (succPriority == optimalValue) {
								optimalLoopSuccPriority = succPriority;
								// Do not break, it may be possible that loop
								// priorities get not involved in priority
								// computation.
							}
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
						m_Logger.debug("Stopped in computeSummarizeEdgePriorties/successors");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}
				// If the current optimal non-loop successor priority not the
				// worst
				// value, also take loop vertices into account.
				if (optimalNonLoopSuccPriority == worstValue) {
					// If non-loop vertices all have the worst value, we must
					// not take loop vertices into account.
					optimalSuccPriority = worstValue;
					m_Logger.debug("\t\tWe do not use loop succesors for priority computation.");
				} else if (optimalNonLoopSuccPriority == SummarizeEdge.NO_PRIORITY) {
					// If value unknown, take the other value.
					optimalSuccPriority = optimalLoopSuccPriority;
				} else if (optimalLoopSuccPriority == SummarizeEdge.NO_PRIORITY) {
					// If value unknown, take the other value.
					optimalSuccPriority = optimalNonLoopSuccPriority;
				} else if (optimalLoopSuccPriority == worstValue) {
					// If value is the worst, take the other value.
					optimalSuccPriority = optimalNonLoopSuccPriority;
				} else if (optimalNonLoopSuccPriority == optimalValue || optimalLoopSuccPriority == optimalValue) {
					// If one has the optimal value, take it.
					optimalSuccPriority = optimalValue;
				} else {
					// In this case both values are 2.
					optimalSuccPriority = 2;
				}
			}

			// Vertex is forced to select the minimum from the optimal
			// successor priority and its own priority
			int searchPriority;
			int searchVertexPriority = searchVertex.getPriority();
			if (optimalSuccPriority != SummarizeEdge.NO_PRIORITY) {
				searchPriority = Math.min(optimalSuccPriority, searchVertexPriority);
			} else {
				searchPriority = searchVertexPriority;
			}

			// Put the search priority for the vertex and decide whether to
			// continue the search for this element
			Integer previousSearchPriorityValue = searchPriorities.put(new Pair<>(searchVertex, searchDownState),
					searchPriority);
			boolean continueSearch = false;
			// Continue search if a search priority is new for the
			// vertex or if values have changed.
			// The search will converge to a fix point since min-method
			// is monotone and the set of priorities is bounded.
			if (previousSearchPriorityValue == null || previousSearchPriorityValue != searchPriority) {
				continueSearch = true;
				m_Logger.debug("\tSetting '" + searchPriority + "' for: " + searchElement);

				// If search element is a duplicator vertex that uses a call
				// transition, then update the priority of the corresponding
				// summarize edges, if existent.
				if (isSearchVertexDuplicatorDD) {
					ETransitionType transitionType = searchVertexAsDuplicatorDD.getTransitionType();
					if (transitionType == ETransitionType.CALL) {
						updateCorrespondingSummarizeEdge(searchElement, searchPriority);
					}
				}
			}

			// If search should be continued, add predecessors to the queue
			if (continueSearch) {
				Set<Vertex<LETTER, STATE>> predecessors = m_GameGraph.getPredecessors(searchVertex);
				if (predecessors != null) {
					for (Vertex<LETTER, STATE> pred : predecessors) {
						// Reject predecessor if it is null
						if (pred == null) {
							continue;
						}
						if (pred instanceof DuplicatorDoubleDeckerVertex) {
							// Predecessor is duplicator vertex
							DuplicatorDoubleDeckerVertex<LETTER, STATE> predAsDuplicatorDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) pred;
							ETransitionType transitionType = predAsDuplicatorDD.getTransitionType();
							if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.RETURN
									|| transitionType == ETransitionType.SINK
									|| transitionType == ETransitionType.SUMMARIZE_ENTRY) {
								// Ignore return and special edges
								continue;
							} else if (transitionType == ETransitionType.CALL) {
								// If right states are not equals, the call is
								// not possible.
								// For example: (q0, q3, c) -> (q0, q4,
								// [q0,q0]), the correct down state must
								// be [q0,q3]. Thus [q0, q0] should not
								// produce new search elements.
								if (!pred.getQ1().equals(searchDownState.getRightDownState())) {
									continue;
								}
								// Right down state changes by using
								// 'duplicator -call-> spoiler'
								Set<VertexDownState<STATE>> downStates = predAsDuplicatorDD.getVertexDownStates();
								// Create search elements for all corresponding
								// correct double decker.
								for (VertexDownState<STATE> downState : downStates) {
									if (downState.getLeftDownState().equals(searchDownState.getLeftDownState())) {
										SummarizeEdge<LETTER, STATE> correspondingEdge = SearchElement
												.computeSummarizeEdge(pred, downState, searchSummarizeEdge,
														invokerToSummarizeEdge);
										searchQueue.add(new SearchElement<LETTER, STATE>(pred, downState,
												searchDownState, correspondingEdge));
									}
								}
							} else if (transitionType == ETransitionType.SUMMARIZE_EXIT) {
								// Follow summarize edge to the source and use
								// this vertex if the edge belongs to the
								// current down state configuration
								Vertex<LETTER, STATE> source = predAsDuplicatorDD.getSummarizeEdge().getSource();
								if (source instanceof SpoilerDoubleDeckerVertex) {
									SpoilerDoubleDeckerVertex<LETTER, STATE> sourceAsSpoilerDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) source;
									if (sourceAsSpoilerDD.hasVertexDownState(searchDownState)) {
										searchQueue.add(new SearchElement<LETTER, STATE>(source, searchDownState,
												searchDownState, searchSummarizeEdge));
									}
								}
							} else {
								// Only add the vertex if the edge belongs to
								// the current down state configuration
								if (predAsDuplicatorDD.hasVertexDownState(searchDownState)) {
									searchQueue.add(new SearchElement<LETTER, STATE>(pred, searchDownState,
											searchDownState, searchSummarizeEdge));
								}
							}
						} else {
							// Predecessor is spoiler vertex
							if (isSearchVertexDuplicatorDD) {
								ETransitionType transitionType = searchVertexAsDuplicatorDD.getTransitionType();
								if (transitionType == ETransitionType.RETURN || transitionType == ETransitionType.SINK
										|| transitionType == ETransitionType.SUMMARIZE_ENTRY
										|| transitionType == ETransitionType.SUMMARIZE_EXIT) {
									// Ignore return and special edges
									break;
								} else if (transitionType == ETransitionType.CALL) {
									if (pred instanceof SpoilerDoubleDeckerVertex) {
										// If left states are not equals, the
										// call is not possible.
										// For example: (q0, q3) -> (q0, q3, c,
										// [q1,q0]), the correct down state must
										// be [q0,q0]. Thus [q1,q0] should not
										// produce new search elements.
										if (!pred.getQ0().equals(searchDownState.getLeftDownState())) {
											continue;
										}
										SpoilerDoubleDeckerVertex<LETTER, STATE> predAsSpoilerDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) pred;
										// Left down state changes by using
										// 'spoiler -call-> duplicator'
										Set<VertexDownState<STATE>> downStates = predAsSpoilerDD.getVertexDownStates();
										// Create search elements for all
										// corresponding correct double decker.
										for (VertexDownState<STATE> downState : downStates) {
											if (downState.getRightDownState()
													.equals(searchDownState.getRightDownState())) {
												SummarizeEdge<LETTER, STATE> correspondingEdge = SearchElement
														.computeSummarizeEdge(pred, downState, searchSummarizeEdge,
																invokerToSummarizeEdge);
												searchQueue.add(new SearchElement<LETTER, STATE>(pred, downState,
														searchDownState, correspondingEdge));
											}
										}
									}
								} else {
									// Only add the vertex if the edge belongs
									// to the current down state configuration
									if (pred instanceof SpoilerDoubleDeckerVertex) {
										SpoilerDoubleDeckerVertex<LETTER, STATE> predAsSpoilerDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) pred;
										if (predAsSpoilerDD.hasVertexDownState(searchDownState)) {
											searchQueue.add(new SearchElement<LETTER, STATE>(pred, searchDownState,
													searchDownState, searchSummarizeEdge));
										}
									}
								}
							}
						}

						// If operation was canceled, for example from the
						// Ultimate framework
						if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
							m_Logger.debug("Stopped in computeSummarizeEdgePriorties/predecessors");
							throw new AutomataOperationCanceledException(this.getClass());
						}
					}
				}
			}
		}

		if (searchCounter.compareTo(maxAmountOfSearches) > 0) {
			throw new IllegalStateException(
					"Computing summarize edge priorities could not be done. The process detected a live lock and aborted.");
		}
	}

	/**
	 * Generates a possible reduced nwa automaton by using the current state of
	 * the game graph that may hold information, usable for reduction, generated
	 * by an {@link ASimulation}.
	 * 
	 * @return A possible reduced nwa automaton
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public INestedWordAutomatonOldApi<LETTER, STATE> generateAutomatonFromGraph()
			throws AutomataOperationCanceledException {
		FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();

		// By default, we assume that there are merge-able states.
		boolean areThereMergeableStates = true;
		if (fairGraph != null) {
			// For fair simulation, we know if there are such states.
			areThereMergeableStates = fairGraph.areThereMergeableStates();
		}
		// By default, we assume that there are no remove-able transitions.
		// Since only fair simulation is capable of such.
		boolean areThereRemoveableTransitions = false;
		List<Triple<STATE, LETTER, STATE>> transitionsToRemove = null;
		if (fairGraph != null) {
			// For fair simulation, we know which transitions
			// need to be removed.
			transitionsToRemove = fairGraph.getTransitionsToRemove();
			areThereRemoveableTransitions = transitionsToRemove != null && !transitionsToRemove.isEmpty();
		}

		Map<STATE, STATE> input2result = null;

		StateFactory<STATE> stateFactory = m_Nwa.getStateFactory();
		NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<>(m_Services, m_Nwa.getInternalAlphabet(),
				m_Nwa.getCallAlphabet(), m_Nwa.getReturnAlphabet(), stateFactory);

		// Merge states
		if (areThereMergeableStates) {
			// Equivalence class that holds all state classes
			// with their representatives
			UnionFind<STATE> equivalenceClasses;

			if (fairGraph != null) {
				// For fair simulation, this was already set up.
				equivalenceClasses = fairGraph.getEquivalenceClasses();
			} else {
				// For other simulation types, we set it up now.
				// Determine which states to merge
				equivalenceClasses = new UnionFind<>();
				for (STATE state : m_Nwa.getStates()) {
					equivalenceClasses.makeEquivalenceClass(state);
				}
				HashRelation<STATE, STATE> similarStates = new HashRelation<>();
				for (SpoilerVertex<LETTER, STATE> v : m_GameGraph.getSpoilerVertices()) {
					// All the states we need are from Spoiler
					if (v.getPM(null, m_GameGraph.getGlobalInfinity()) < m_GameGraph.getGlobalInfinity()) {
						boolean considerVertex = true;
						// For delayed simulation we need to choose between the
						// vertex with bit set to true or false
						if (m_SimulationType == ESimulationType.DELAYED) {
							if (v.isB()) {
								considerVertex = m_Nwa.isFinal(v.getQ0()) && !m_Nwa.isFinal(v.getQ0());
							} else {
								considerVertex = !m_Nwa.isFinal(v.getQ0()) || m_Nwa.isFinal(v.getQ0());
							}
						}
						if (considerVertex) {
							STATE state1 = v.getQ0();
							STATE state2 = v.getQ1();
							if (state1 != null && state2 != null) {
								similarStates.addPair(state1, state2);
							}
						}
					}
				}
				// Mark states for merge if they simulate each other
				for (STATE state1 : similarStates.getDomain()) {
					for (STATE state2 : similarStates.getImage(state1)) {
						// Only merge if simulation holds in both directions
						if (similarStates.containsPair(state2, state1)) {
							equivalenceClasses.union(state1, state2);
						}
					}
				}

				if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
					m_Logger.debug("Stopped in generateBuchiAutomatonFromGraph/equivalenceClasses");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}

			// Calculate initial states
			Set<STATE> representativesOfInitials = new HashSet<>();
			for (STATE initialState : m_Nwa.getInitialStates()) {
				representativesOfInitials.add(equivalenceClasses.find(initialState));
			}
			// Calculate final states
			Set<STATE> representativesOfFinals = new HashSet<>();
			for (STATE finalState : m_Nwa.getFinalStates()) {
				representativesOfFinals.add(equivalenceClasses.find(finalState));
			}

			// If operation was canceled, for example from the
			// Ultimate framework
			if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
				m_Logger.debug("Stopped in generateBuchiAutomatonFromGraph/state calculation finished");
				throw new AutomataOperationCanceledException(this.getClass());
			}

			// Add states
			input2result = new HashMap<>(m_Nwa.size());
			for (STATE representative : equivalenceClasses.getAllRepresentatives()) {
				boolean isInitial = representativesOfInitials.contains(representative);
				boolean isFinal = representativesOfFinals.contains(representative);
				Set<STATE> eqClass = equivalenceClasses.getEquivalenceClassMembers(representative);
				STATE mergedState = stateFactory.minimize(eqClass);
				result.addState(isInitial, isFinal, mergedState);
				increaseResultAmountOfStates();
				for (STATE eqClassMember : eqClass) {
					input2result.put(eqClassMember, mergedState);
				}
			}
		} else {
			// If there is no merge-able state simply
			// copy the inputed automaton
			for (STATE state : m_Nwa.getStates()) {
				boolean isInitial = m_Nwa.isInitial(state);
				boolean isFinal = m_Nwa.isFinal(state);
				result.addState(isInitial, isFinal, state);
				increaseResultAmountOfStates();
			}
		}

		// Add transitions
		for (STATE inputSrc : m_Nwa.getStates()) {
			STATE resultSrc;
			if (areThereMergeableStates) {
				// Only access field if it was initialized
				resultSrc = input2result.get(inputSrc);
			} else {
				resultSrc = inputSrc;
			}
			// Internal transitions
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Nwa.internalSuccessors(inputSrc)) {
				LETTER a = outTrans.getLetter();
				STATE inputDest = outTrans.getSucc();
				STATE resultDest;
				if (areThereMergeableStates) {
					// Only access field if it was initialized
					resultDest = input2result.get(inputDest);
				} else {
					resultDest = inputDest;
				}

				if (areThereRemoveableTransitions) {
					// Skip edges that should get removed
					Triple<STATE, LETTER, STATE> transAsTriple = new Triple<>(inputSrc, a, inputDest);
					if (transitionsToRemove != null && !transitionsToRemove.contains(transAsTriple)) {
						result.addInternalTransition(resultSrc, a, resultDest);
						increaseResultAmountOfTransitions();
					}
				} else {
					// If there is no removable transition simply copy the
					// inputed automaton
					result.addInternalTransition(resultSrc, a, resultDest);
					increaseResultAmountOfTransitions();
				}
			}
			// Call transitions
			for (OutgoingCallTransition<LETTER, STATE> outTrans : m_Nwa.callSuccessors(inputSrc)) {
				LETTER a = outTrans.getLetter();
				STATE inputDest = outTrans.getSucc();
				STATE resultDest;
				if (areThereMergeableStates) {
					// Only access field if it was initialized
					resultDest = input2result.get(inputDest);
				} else {
					resultDest = inputDest;
				}

				if (areThereRemoveableTransitions) {
					// Skip edges that should get removed
					// TODO This data structure needs information about
					// transition types, or it may not be able to differentiate
					// between initial and call edge if they share
					// the same alphabet.
					Triple<STATE, LETTER, STATE> transAsTriple = new Triple<>(inputSrc, a, inputDest);
					if (transitionsToRemove != null && !transitionsToRemove.contains(transAsTriple)) {
						result.addCallTransition(resultSrc, a, resultDest);
						increaseResultAmountOfTransitions();
					}
				} else {
					// If there is no removable transition simply copy the
					// inputed automaton
					result.addCallTransition(resultSrc, a, resultDest);
					increaseResultAmountOfTransitions();
				}
			}
			// Return transitions
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : m_Nwa.returnSuccessors(inputSrc)) {
				LETTER a = outTrans.getLetter();
				STATE inputDest = outTrans.getSucc();
				STATE inputHierPred = outTrans.getHierPred();
				STATE resultDest;
				STATE resultHierPred;
				if (areThereMergeableStates) {
					// Only access field if it was initialized
					resultDest = input2result.get(inputDest);
					resultHierPred = input2result.get(inputHierPred);
				} else {
					resultDest = inputDest;
					resultHierPred = inputHierPred;
				}

				if (areThereRemoveableTransitions) {
					// Skip edges that should get removed
					// TODO This data structure needs information about
					// transition types and hierPred, or it may not be able to
					// differentiate between initial and return edge if
					// they share the same alphabet.
					Triple<STATE, LETTER, STATE> transAsTriple = new Triple<>(inputSrc, a, inputDest);
					if (transitionsToRemove != null && !transitionsToRemove.contains(transAsTriple)) {
						result.addReturnTransition(resultSrc, resultHierPred, a, resultDest);
						increaseResultAmountOfTransitions();
					}
				} else {
					// If there is no removable transition simply copy the
					// inputed automaton
					result.addReturnTransition(resultSrc, resultHierPred, a, resultDest);
					increaseResultAmountOfTransitions();
				}
			}
		}

		// Log remaining performance stuff
		m_SimulationPerformance.setCountingMeasure(ECountingMeasure.REMOVED_STATES,
				m_SimulationPerformance.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES)
						- m_ResultAmountOfStates);
		m_SimulationPerformance.setCountingMeasure(ECountingMeasure.REMOVED_TRANSITIONS,
				m_SimulationPerformance.getCountingMeasureResult(ECountingMeasure.BUCHI_TRANSITIONS)
						- m_ResultAmountOfTransitions);

		// If operation was canceled, for example from the
		// Ultimate framework
		if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
			m_Logger.debug("Stopped in generateBuchiAutomatonFromGraph/states and transitions added");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		// Remove unreachable states which can occur due to transition removal
		if (areThereRemoveableTransitions) {
			NestedWordAutomatonReachableStates<LETTER, STATE> nwaReachableStates = new RemoveUnreachable<LETTER, STATE>(
					m_Services, result).getResult();
			return nwaReachableStates;
		} else {
			return result;
		}
	}

	/**
	 * Generates the game graph out of an original nwa automaton. The graph
	 * represents a game, see {@link AGameGraph}.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateGameGraphFromAutomaton() throws AutomataOperationCanceledException {
		m_SimulationPerformance.startTimeMeasure(ETimeMeasure.BUILD_GRAPH);

		generateVertices();
		generateRegularEdges();

		m_SimulationPerformance.startTimeMeasure(ETimeMeasure.COMPUTE_SAFE_VERTEX_DOWN_STATES);
		computeSafeVertexDownStates();
		m_SimulationPerformance.stopTimeMeasure(ETimeMeasure.COMPUTE_SAFE_VERTEX_DOWN_STATES);

		m_SimulationPerformance.startTimeMeasure(ETimeMeasure.GENERATE_SUMMARIZE_EDGES);
		generateSummarizeEdges();
		m_SimulationPerformance.stopTimeMeasure(ETimeMeasure.GENERATE_SUMMARIZE_EDGES);

		m_SimulationPerformance.startTimeMeasure(ETimeMeasure.COMPUTE_SUMMARIZE_EDGE_PRIORITIES);
		computeSummarizeEdgePriorities();
		m_SimulationPerformance.stopTimeMeasure(ETimeMeasure.COMPUTE_SUMMARIZE_EDGE_PRIORITIES);

		clear();

		m_SimulationPerformance.stopTimeMeasure(ETimeMeasure.BUILD_GRAPH);
	}

	/**
	 * Generates the regular edges of the game graph from the input automaton.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateRegularEdges() throws AutomataOperationCanceledException {
		m_Logger.debug("Generating regular edges.");
		for (STATE edgeDest : m_Nwa.getStates()) {
			// Edges generated by internal transitions
			for (IncomingInternalTransition<LETTER, STATE> trans : m_Nwa.internalPredecessors(edgeDest)) {
				m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS);

				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -a-> q2 : (x, q1, a) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false,
							ETransitionType.INTERNAL, null, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (src != null && dest != null) {
						// Do not add if using direct simulation and the
						// destination represents a vertex where Duplicator
						// directly looses.
						if (m_SimulationType != ESimulationType.DIRECT || !doesLooseInDirectSim(fixState, edgeDest)) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						}
					}
					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (m_SimulationType == ESimulationType.DELAYED) {
						src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), true,
								ETransitionType.INTERNAL, null, null);
						if (!m_Nwa.isFinal(edgeDest) && getAmountOfBitsForSpoilerVertices(fixState, edgeDest) > 1) {
							dest = getSpoilerVertex(fixState, edgeDest, true, null, null);
						} else {
							dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
						}
						if (src != null && dest != null) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						}
					}

					// Spoiler edges q1 -a-> q2 : (q1, x) -> (q2, x, a)
					src = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, ETransitionType.INTERNAL,
							null, null);
					if (src != null && dest != null) {
						// Do not add if using direct simulation and the
						// destination represents a vertex where Duplicator
						// directly looses.
						if (m_SimulationType != ESimulationType.DIRECT
								|| !doesLooseInDirectSim(trans.getPred(), fixState)) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						}
					}
					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (m_SimulationType == ESimulationType.DELAYED) {
						dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true,
								ETransitionType.INTERNAL, null, null);
						if (getAmountOfBitsForSpoilerVertices(trans.getPred(), fixState) > 1) {
							src = getSpoilerVertex(trans.getPred(), fixState, true, null, null);
							if (src != null && dest != null) {
								m_GameGraph.addEdge(src, dest);
								m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							}
						}
						if (m_Nwa.isFinal(edgeDest)) {
							src = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
							if (src != null && dest != null) {
								m_GameGraph.addEdge(src, dest);
								m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							}
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
						m_Logger.debug("Stopped in generateGameGraphFromAutomaton/generating internal edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// Add the processed transition to the internal field, if using
				// fair simulation
				addAutomatonTransitionToInternalField(new Triple<>(trans.getPred(), trans.getLetter(), edgeDest));
			}

			// Edges generated by call transitions
			for (IncomingCallTransition<LETTER, STATE> trans : m_Nwa.callPredecessors(edgeDest)) {
				m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS);

				// Calling is possible regardless of the stack
				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -c-> q2 : (x, q1, c) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), false,
							ETransitionType.CALL, null, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					if (src != null && dest != null) {
						// Do not add if using direct simulation and the
						// destination represents a vertex where Duplicator
						// directly looses.
						if (m_SimulationType != ESimulationType.DIRECT || !doesLooseInDirectSim(fixState, edgeDest)) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						}
					}
					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (m_SimulationType == ESimulationType.DELAYED) {
						src = getDuplicatorVertex(fixState, trans.getPred(), trans.getLetter(), true,
								ETransitionType.CALL, null, null);
						if (!m_Nwa.isFinal(edgeDest) && getAmountOfBitsForSpoilerVertices(fixState, edgeDest) > 1) {
							dest = getSpoilerVertex(fixState, edgeDest, true, null, null);
						} else {
							dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
						}
						if (src != null && dest != null) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						}
					}

					// Spoiler edges q1 -c-> q2 : (q1, x) -> (q2, x, c)
					src = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, ETransitionType.CALL, null,
							null);
					if (src != null && dest != null) {
						// Do not add if using direct simulation and the
						// destination represents a vertex where Duplicator
						// directly looses.
						if (m_SimulationType != ESimulationType.DIRECT
								|| !doesLooseInDirectSim(trans.getPred(), fixState)) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						}
					}
					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (m_SimulationType == ESimulationType.DELAYED) {
						dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true, ETransitionType.CALL,
								null, null);
						if (getAmountOfBitsForSpoilerVertices(trans.getPred(), fixState) > 1) {
							src = getSpoilerVertex(trans.getPred(), fixState, true, null, null);
							if (src != null && dest != null) {
								m_GameGraph.addEdge(src, dest);
								m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							}
						}
						if (m_Nwa.isFinal(edgeDest)) {
							src = getSpoilerVertex(trans.getPred(), fixState, false, null, null);
							if (src != null && dest != null) {
								m_GameGraph.addEdge(src, dest);
								m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							}
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
						m_Logger.debug("Stopped in generateGameGraphFromAutomaton/generating call edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// TODO Find a way that buechi transitions support nwa
				// transitions, call and return with hierPred
				// getBuechiTransitions().add(new Triple<>(trans.getPred(),
				// trans.getLetter(), edgeDest));
			}

			// Edges generated by return transitions
			for (IncomingReturnTransition<LETTER, STATE> trans : m_Nwa.returnPredecessors(edgeDest)) {
				m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.BUCHI_TRANSITIONS);

				for (STATE fixState : m_Nwa.getStates()) {
					// Duplicator edges q1 -r/q0-> q2 : (x, q1, r/q0) -> (x, q2)
					Vertex<LETTER, STATE> src = getDuplicatorVertex(fixState, trans.getLinPred(), trans.getLetter(),
							false, ETransitionType.RETURN, null, null);
					Vertex<LETTER, STATE> dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
					// Ensure that the edge represents a possible move.
					// This is when the hierPred state is a down state of q1
					boolean isEdgePossible = hasDownState(trans.getLinPred(), trans.getHierPred());
					if (src != null && dest != null && isEdgePossible) {
						// Do not add if using direct simulation and the
						// destination represents a vertex where Duplicator
						// directly looses.
						if (m_SimulationType != ESimulationType.DIRECT || !doesLooseInDirectSim(fixState, edgeDest)) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						} else {
							// Instead remember it as omitted edge because we
							// may need it for correct push-over edge generation
							List<Vertex<LETTER, STATE>> omittedSuccessors = m_ReturnInvokerOmittedSuccessors.get(src);
							if (omittedSuccessors == null) {
								omittedSuccessors = new LinkedList<>();
							}
							omittedSuccessors.add(dest);
							m_ReturnInvokerOmittedSuccessors.put(src, omittedSuccessors);
						}

						// Remember vertex since we need it later for summarize
						// edge generation
						if (src instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
							m_DuplicatorReturningVertices.add((DuplicatorDoubleDeckerVertex<LETTER, STATE>) src);
						}
					}
					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (m_SimulationType == ESimulationType.DELAYED) {
						src = getDuplicatorVertex(fixState, trans.getLinPred(), trans.getLetter(), true,
								ETransitionType.RETURN, null, null);
						if (!m_Nwa.isFinal(edgeDest) && getAmountOfBitsForSpoilerVertices(fixState, edgeDest) > 1) {
							dest = getSpoilerVertex(fixState, edgeDest, true, null, null);
						} else {
							dest = getSpoilerVertex(fixState, edgeDest, false, null, null);
						}
						if (src != null && dest != null && isEdgePossible) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							// Remember vertex since we need it later for
							// summarize
							// edge generation
							if (src instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
								m_DuplicatorReturningVertices.add((DuplicatorDoubleDeckerVertex<LETTER, STATE>) src);
							}
						}
					}

					// Spoiler edges q1 -r/q0-> q2 : (q1, x) -> (q2, x, r/q0)
					src = getSpoilerVertex(trans.getLinPred(), fixState, false, null, null);
					dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), false, ETransitionType.RETURN,
							null, null);
					// Ensure that the edge represents a possible move.
					// This is when the hierPred state is a down state of q1
					isEdgePossible = hasDownState(trans.getLinPred(), trans.getHierPred());
					if (src != null && dest != null && isEdgePossible) {
						// Do not add if using direct simulation and the
						// destination represents a vertex where Duplicator
						// directly looses.
						if (m_SimulationType != ESimulationType.DIRECT
								|| !doesLooseInDirectSim(trans.getLinPred(), fixState)) {
							m_GameGraph.addEdge(src, dest);
							m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
						} else {
							// Instead remember it as omitted edge because we
							// may need it for correct push-over edge generation
							List<Vertex<LETTER, STATE>> omittedPredecessors = m_ReturnInvokerOmittedPredecessors.get(src);
							if (omittedPredecessors == null) {
								omittedPredecessors = new LinkedList<>();
							}
							omittedPredecessors.add(dest);
							m_ReturnInvokerOmittedSuccessors.put(src, omittedPredecessors);
						}
					}
					// For delayed simulation we also need to account for
					// vertices with the bit set to true
					if (m_SimulationType == ESimulationType.DELAYED) {
						dest = getDuplicatorVertex(edgeDest, fixState, trans.getLetter(), true, ETransitionType.RETURN,
								null, null);
						if (getAmountOfBitsForSpoilerVertices(trans.getLinPred(), fixState) > 1) {
							src = getSpoilerVertex(trans.getLinPred(), fixState, true, null, null);
							if (src != null && dest != null && isEdgePossible) {
								m_GameGraph.addEdge(src, dest);
								m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							}
						}
						if (m_Nwa.isFinal(edgeDest)) {
							src = getSpoilerVertex(trans.getLinPred(), fixState, false, null, null);
							if (src != null && dest != null && isEdgePossible) {
								m_GameGraph.addEdge(src, dest);
								m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.GAMEGRAPH_EDGES);
							}
						}
					}

					// If operation was canceled, for example from the
					// Ultimate framework
					if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
						m_Logger.debug("Stopped in generateGameGraphFromAutomaton/generating return edges");
						throw new AutomataOperationCanceledException(this.getClass());
					}
				}

				// TODO Find a way that buechi transitions support nwa
				// transitions, call and return with hierPred
				// getBuechiTransitions().add(new Triple<>(trans.getPred(),
				// trans.getLetter(), edgeDest));
			}
		}
	}

	/**
	 * Generates the summarize edges of the game graph from the input automaton.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateSummarizeEdges() throws AutomataOperationCanceledException {
		m_Logger.debug("Generating summarize edges.");
		LoopDetector<LETTER, STATE> loopDetector = new LoopDetector<>(m_GameGraph, m_Logger, m_ProgressTimer);

		// Return edges (q', q1 [q5, q6]) -> (q0, q1, r/q2) -> (q0, q3) lead
		// to creation of summarize edge (q5, q6) -> (q0, q3)
		for (DuplicatorDoubleDeckerVertex<LETTER, STATE> returnInvoker : m_DuplicatorReturningVertices) {
			Set<Vertex<LETTER, STATE>> summarizeDestinations = m_GameGraph.getSuccessors(returnInvoker);
			if (summarizeDestinations == null) {
				// Ignore this summarize edges if they have no destinations.
				// This can happen in direct simulation, where connections to
				// destinations get deleted if they represent a move where
				// Duplicator would directly loose.
				continue;
			}
			for (Vertex<LETTER, STATE> summarizeDest : summarizeDestinations) {
				if (!(summarizeDest instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
					continue;
				}
				SpoilerDoubleDeckerVertex<LETTER, STATE> summarizeDestAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) summarizeDest;
				Set<Vertex<LETTER, STATE>> preInvokers = m_GameGraph.getPredecessors(returnInvoker);
				if (preInvokers == null) {
					// Ignore this summarize edge destination if it has no pre
					// invokers.
					// This can happen in direct simulation, where connections
					// to pre invokers get deleted if they represent a move
					// where Duplicator would directly loose.
					continue;
				}
				for (Vertex<LETTER, STATE> preInvoker : preInvokers) {
					if (!(preInvoker instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
						continue;
					}
					SpoilerDoubleDeckerVertex<LETTER, STATE> preInvokerAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) preInvoker;
					for (VertexDownState<STATE> vertexDownState : preInvokerAsDD.getVertexDownStates()) {
						// If vertex down state [q, q'] does not contain
						// bottom then use the corresponding vertex as source
						// of the summarize edge
						STATE leftDownState = vertexDownState.getLeftDownState();
						STATE rightDownState = vertexDownState.getRightDownState();
						if (leftDownState.equals(m_Bottom) || rightDownState.equals(m_Bottom)) {
							continue;
						}

						// In the standard case we use the false bit.
						SpoilerVertex<LETTER, STATE> summarizeSrcFalseBit = getSpoilerVertex(leftDownState,
								rightDownState, false, null, null);
						// In the standard case this vertex must be able to
						// reach the destination.
						boolean canFalseBitReachDestination = true;
						// In delayed simulation there may be up to two sources,
						// differentiating in the bit, depending on if they can
						// reach the destination.
						if (m_SimulationType == ESimulationType.DELAYED) {
							// TODO This check is expensive, there may be better
							// ways to solve the problem
							canFalseBitReachDestination = loopDetector.canVertexReachDestination(summarizeSrcFalseBit,
									summarizeDestAsDD);
						}

						// False bit summarize edge
						if (m_SimulationType != ESimulationType.DELAYED || canFalseBitReachDestination) {
							SpoilerVertex<LETTER, STATE> summarizeSrc = summarizeSrcFalseBit;
							if (summarizeSrc == null || !(summarizeSrc instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
								continue;
							}
							SpoilerDoubleDeckerVertex<LETTER, STATE> summarizeSrcAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) summarizeSrc;
							// Do not add the edge if the source or destination
							// is a Spoiler vertex where Duplicator directly
							// looses in direct simulation, if he uses the edge.
							if (m_SimulationType == ESimulationType.DIRECT
									&& (doesLooseInDirectSim(summarizeSrcAsDD.getQ0(), summarizeSrcAsDD.getQ1())
											|| doesLooseInDirectSim(summarizeDestAsDD.getQ0(),
													summarizeDestAsDD.getQ1()))) {
								continue;
							}
							addSummarizeEdge(summarizeSrcAsDD, summarizeDestAsDD, preInvokerAsDD);
						}
						// True bit summarize edge
						if (m_SimulationType == ESimulationType.DELAYED) {
							SpoilerVertex<LETTER, STATE> summarizeSrcTrueBit = getSpoilerVertex(leftDownState,
									rightDownState, true, null, null);
							// TODO This check is expensive, there may be better
							// ways to solve the problem
							boolean canTrueBitReachDestination = loopDetector
									.canVertexReachDestination(summarizeSrcTrueBit, summarizeDestAsDD);
							if (canTrueBitReachDestination) {
								SpoilerVertex<LETTER, STATE> summarizeSrc = summarizeSrcTrueBit;
								if (summarizeSrc == null
										|| !(summarizeSrc instanceof SpoilerDoubleDeckerVertex<?, ?>)) {
									continue;
								}
								SpoilerDoubleDeckerVertex<LETTER, STATE> summarizeSrcAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) summarizeSrc;
								// Do not add the edge if the source or
								// destination
								// is a Spoiler vertex where Duplicator directly
								// looses in direct simulation,
								// if he uses the edge.
								if (m_SimulationType == ESimulationType.DIRECT
										&& (doesLooseInDirectSim(summarizeSrcAsDD.getQ0(), summarizeSrcAsDD.getQ1())
												|| doesLooseInDirectSim(summarizeDestAsDD.getQ0(),
														summarizeDestAsDD.getQ1()))) {
									continue;
								}
								addSummarizeEdge(summarizeSrcAsDD, summarizeDestAsDD, preInvokerAsDD);
							}
						}
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
					m_Logger.debug("Stopped in generateGameGraphFromAutomaton/generating summarize edges");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}

		// Delete all incoming and outgoing edges of the invoker since they are
		// covered by summarize edges
		for (DuplicatorDoubleDeckerVertex<LETTER, STATE> returnInvoker : m_DuplicatorReturningVertices) {
			Set<Vertex<LETTER, STATE>> successors = m_GameGraph.getSuccessors(returnInvoker);
			List<Vertex<LETTER, STATE>> successorsToProcess = null;
			if (successors != null) {
				// Care for concurrentModifcationException
				successorsToProcess = new LinkedList<>(successors);
				for (Vertex<LETTER, STATE> succ : successorsToProcess) {
					m_GameGraph.removeEdge(returnInvoker, succ);
				}
			}
			Set<Vertex<LETTER, STATE>> predecessors = m_GameGraph.getPredecessors(returnInvoker);
			List<Vertex<LETTER, STATE>> predecessorsToProcess = null;
			if (predecessors != null) {
				// Care for concurrentModifcationException
				predecessorsToProcess = new LinkedList<>(predecessors);
				for (Vertex<LETTER, STATE> pred : predecessorsToProcess) {
					m_GameGraph.removeEdge(pred, returnInvoker);
					// Care for dead end spoiler vertices because they are not
					// allowed in a legal game graph.
					// They need to form a legal instant win for Duplicator.
					if (!m_GameGraph.hasSuccessors(pred) && pred instanceof SpoilerDoubleDeckerVertex<?, ?>) {
						SpoilerDoubleDeckerVertex<LETTER, STATE> preAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) pred;
						addDuplicatorWinningSink(preAsDD);
					}
				}
			}
			// Remove not reachable vertex
			removeDuplicatorVertex(returnInvoker);

			// Add push-over edges that are generated by the return invoker
			if (m_SimulationType == ESimulationType.DIRECT) {
				// Care for omitted edges that may occur in direct simulation if a vertex is directly loosing.
				if (successorsToProcess == null) {
					successorsToProcess = new LinkedList<Vertex<LETTER, STATE>>();
				}
				List<Vertex<LETTER, STATE>> omittedSuccessors = m_ReturnInvokerOmittedSuccessors.get(returnInvoker);
				if (omittedSuccessors != null) {
					successorsToProcess.addAll(omittedSuccessors);
				}
				if (predecessorsToProcess == null) {
					predecessorsToProcess = new LinkedList<Vertex<LETTER, STATE>>();
				}
				List<Vertex<LETTER, STATE>> omittedPredecessors = m_ReturnInvokerOmittedPredecessors.get(returnInvoker);
				if (omittedPredecessors != null) {
					predecessorsToProcess.addAll(omittedPredecessors);
				}
			}
			// Create push-over edges for every pair of successors and predecessors
			if (successorsToProcess != null && predecessorsToProcess != null) {
				for (Vertex<LETTER, STATE> succ : successorsToProcess) {
					for (Vertex<LETTER, STATE> pred : predecessorsToProcess) {
						m_GameGraph.addPushOverEdge(pred, succ);
					}
				}
			}
		}
	}

	/**
	 * Generates the vertices of the game graph from the input automaton.
	 * 
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void generateVertices() throws AutomataOperationCanceledException {
		m_Logger.debug("Generating vertices.");
		VertexDownState<STATE> bottomBoth = new VertexDownState<STATE>(m_Bottom, m_Bottom);
		int duplicatorPriority = 2;
		// In direct simulation, every duplicator vertex has a priority of zero
		if (m_SimulationType == ESimulationType.DIRECT) {
			duplicatorPriority = 0;
		}

		for (STATE leftState : m_Nwa.getStates()) {
			m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.BUCHI_STATES);

			for (STATE rightState : m_Nwa.getStates()) {
				// Generate Spoiler vertices (leftState, rightState)
				int priority = calculatePriority(leftState, rightState);
				if (priority == 1) {
					m_GameGraph.increaseGlobalInfinity();
				}

				SpoilerDoubleDeckerVertex<LETTER, STATE> spoilerVertex = null;
				// In delayed simulation we always generate the vertex with
				// priority zero. Conditionally we also add a vertex with
				// priority one.
				if (m_SimulationType == ESimulationType.DELAYED) {
					spoilerVertex = new SpoilerDoubleDeckerVertex<>(0, false, leftState, rightState);
				} else {
					spoilerVertex = new SpoilerDoubleDeckerVertex<>(priority, false, leftState, rightState);
				}

				applyVertexDownStatesToVertex(spoilerVertex);
				// Memorize vertices that have down state
				// configurations of [bottom, bottom]
				if (spoilerVertex.hasVertexDownState(bottomBoth)) {
					// It is enough to only add spoiler vertices since the goal.
					// Duplicator vertices that have [bottom, bottom] are always
					// reachable from a spoiler vertex with [bottom, bottom]
					// since duplicator vertices with no predecessors do not
					// exist in our game graphs.
					m_BottomVertices.add(spoilerVertex);
				}
				addSpoilerVertex(spoilerVertex);
				// In delayed simulation we may also add a vertex with
				// priority one that has the bit set to true.
				if (m_SimulationType == ESimulationType.DELAYED) {
					if (priority == 1) {
						spoilerVertex = new SpoilerDoubleDeckerVertex<>(priority, true, leftState, rightState);
						applyVertexDownStatesToVertex(spoilerVertex);
						if (spoilerVertex.hasVertexDownState(bottomBoth)) {
							m_BottomVertices.add(spoilerVertex);
						}
						addSpoilerVertex(spoilerVertex);
					}
				}

				// Generate Duplicator vertices (leftState, rightState, letter)
				// Vertices generated by internal transitions
				for (LETTER letter : m_Nwa.lettersInternalIncoming(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(
							duplicatorPriority, false, leftState, rightState, letter, ETransitionType.INTERNAL);
					applyVertexDownStatesToVertex(duplicatorVertex);
					addDuplicatorVertex(duplicatorVertex);
					if (m_SimulationType == ESimulationType.DELAYED) {
						duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(duplicatorPriority, true, leftState,
								rightState, letter, ETransitionType.INTERNAL);
						applyVertexDownStatesToVertex(duplicatorVertex);
						addDuplicatorVertex(duplicatorVertex);
					}
				}
				// Vertices generated by call transitions
				for (LETTER letter : m_Nwa.lettersCallIncoming(leftState)) {
					DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(
							duplicatorPriority, false, leftState, rightState, letter, ETransitionType.CALL);
					applyVertexDownStatesToVertex(duplicatorVertex);
					addDuplicatorVertex(duplicatorVertex);
					if (m_SimulationType == ESimulationType.DELAYED) {
						duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(duplicatorPriority, true, leftState,
								rightState, letter, ETransitionType.CALL);
						applyVertexDownStatesToVertex(duplicatorVertex);
						addDuplicatorVertex(duplicatorVertex);
					}
				}
				// Vertices generated by return transitions
				for (IncomingReturnTransition<LETTER, STATE> transition : m_Nwa.returnPredecessors(leftState)) {
					// Only create vertex if the return transition is
					// possible to go from here.
					// That is when in (q0, q1) -> (q2, q1, r/q3),
					// q0 has q3 as down state
					if (hasDownState(transition.getLinPred(), transition.getHierPred())) {
						// Only add if not already existent
						if (getDuplicatorVertex(leftState, rightState, transition.getLetter(), false,
								ETransitionType.RETURN, null, null) == null) {
							DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(
									duplicatorPriority, false, leftState, rightState, transition.getLetter(),
									ETransitionType.RETURN);
							applyVertexDownStatesToVertex(duplicatorVertex);
							addDuplicatorVertex(duplicatorVertex);
						}
						if (m_SimulationType == ESimulationType.DELAYED) {
							// Only add if not already existent
							if (getDuplicatorVertex(leftState, rightState, transition.getLetter(), true,
									ETransitionType.RETURN, null, null) == null) {
								DuplicatorDoubleDeckerVertex<LETTER, STATE> duplicatorVertex = new DuplicatorDoubleDeckerVertex<>(
										duplicatorPriority, true, leftState, rightState, transition.getLetter(),
										ETransitionType.RETURN);
								applyVertexDownStatesToVertex(duplicatorVertex);
								addDuplicatorVertex(duplicatorVertex);
							}
						}
					}
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (m_ProgressTimer != null && !m_ProgressTimer.continueProcessing()) {
					m_Logger.debug("Stopped in generateGameGraphFromAutomaton/generating vertices");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}

			// Generate an equivalence class for every state from
			// the nwa automaton, if fair simulation
			makeEquivalenceClass(leftState);
		}

		// Increase by one, global infinity is amount of priority one + 1
		m_GameGraph.increaseGlobalInfinity();
	}

	/**
	 * Gets a Duplicator vertex by its signature. See
	 * {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 * 
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param a
	 *            Used letter
	 * @param bit
	 *            Extra bit of the vertex
	 * @param transType
	 *            Type of the transition
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to if the transition is of
	 *            type {@link ETransitionType#SUMMARIZE_ENTRY} or
	 *            {@link ETransitionType#SUMMARIZE_EXIT}. Use <tt>null</tt> if
	 *            that is not the case.
	 * @param sink
	 *            Sink the vertex belongs to if the transition is of type
	 *            {@link ETransitionType#SINK}. Use <tt>null</tt> if that is not
	 *            the case.
	 * @return The duplicator vertex associated to the given signature. See
	 *         {@link #getDuplicatorVertex(Object, Object, Object, boolean)}.
	 */
	public DuplicatorVertex<LETTER, STATE> getDuplicatorVertex(final STATE q0, final STATE q1, final LETTER a,
			final boolean bit, final ETransitionType transType, final SummarizeEdge<LETTER, STATE> summarizeEdge,
			final DuplicatorWinningSink<LETTER, STATE> sink) {
		return m_AutomatonStatesToGraphDuplicatorVertex.get(new Hep<>(q0, q1, a, bit, transType, summarizeEdge, sink));
	}

	/**
	 * Gets the performance log of this object.
	 * 
	 * @return Performance log of this object
	 */
	public SimulationPerformance getSimulationPerformance() {
		return m_SimulationPerformance;
	}

	/**
	 * Gets a Spoiler vertex by its signature. See
	 * {@link #getSpoilerVertex(Object, Object, boolean)}.
	 * 
	 * @param q0
	 *            Left state
	 * @param q1
	 *            Right state
	 * @param bit
	 *            Extra bit of the vertex
	 * @param transType
	 *            Type of the transition
	 * @param summarizeEdge
	 *            Summarize edge the vertex belongs to. Use <tt>null</tt> if the
	 *            vertex does not belong to one. This is used for special
	 *            vertices that are used to represent a summary edge correctly
	 *            for a valid game graph.
	 * @param sink
	 *            Sink the vertex belongs to. Use <tt>null</tt> if the vertex
	 *            does not belong to one. This is used for special vertices that
	 *            are used to represent a sink correctly for a valid game graph.
	 * @return The spoiler vertex associated to the given signature. See
	 *         {@link #getSpoilerVertex(Object, Object, boolean)}.
	 */
	public SpoilerVertex<LETTER, STATE> getSpoilerVertex(final STATE q0, final STATE q1, final boolean bit,
			final SummarizeEdge<LETTER, STATE> summarizeEdge, final DuplicatorWinningSink<LETTER, STATE> sink) {
		return m_AutomatonStatesToGraphSpoilerVertex.get(new Quin<>(q0, q1, bit, summarizeEdge, sink));
	}

	/**
	 * Adds a given transition to the internal field of buechi transitions, if
	 * fair simulation.
	 * 
	 * @param transition
	 *            Transition to add
	 */
	private void addAutomatonTransitionToInternalField(final Triple<STATE, LETTER, STATE> transition) {
		FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();
		if (fairGraph != null) {
			fairGraph.getBuechiTransitions().add(transition);
		}
	}

	/**
	 * Creates and adds a duplicator winning sink to the given sink entry. To
	 * form a valid edge it creates a pair of two states after the entry. In
	 * detail this will be: <b>sinkEntry -> DuplicatorSink -> SpoilerSink ->
	 * DuplicatorSink -> ...</b>. <br/>
	 * <br/>
	 * The SpoilerSink will have a priority of 0 to form a winning vertex for
	 * Duplicator.
	 * 
	 * @param sinkEntry
	 *            Entry vertex of the sink
	 */
	private void addDuplicatorWinningSink(final SpoilerDoubleDeckerVertex<LETTER, STATE> sinkEntry) {
		// Only add if not already existent
		if (m_EntryToSink.get(sinkEntry) == null) {
			DuplicatorWinningSink<LETTER, STATE> sink = new DuplicatorWinningSink<>(sinkEntry);
			m_EntryToSink.put(sinkEntry, sink);

			DuplicatorVertex<LETTER, STATE> duplicatorSink = sink.getDuplicatorSink();
			SpoilerVertex<LETTER, STATE> spoilerSink = sink.getSpoilerSink();

			// Add shadow vertices
			addDuplicatorVertex(duplicatorSink);
			addSpoilerVertex(spoilerSink);

			// Add edges connecting the sink
			m_GameGraph.addEdge(sinkEntry, duplicatorSink);
			m_GameGraph.addEdge(duplicatorSink, spoilerSink);
			m_GameGraph.addEdge(spoilerSink, duplicatorSink);
		}
	}

	/**
	 * Creates and adds a summarize edge with given source and destination. To
	 * form a valid edge it creates a pair of three states between source and
	 * destination. In detail this will be: <b>src -> DuplicatorShadowVertex1 ->
	 * SpoilerShadowVertex -> DuplicatorShadowVertex2 -> dest</b>. <br/>
	 * <br/>
	 * The SpoilerShadowVertex will have no priority by default, it must be
	 * taken care of this afterwards.
	 * 
	 * @param src
	 *            Source of the summarize edge
	 * @param dest
	 *            Destination of the summarize edge
	 * @param spoilerInvoker
	 *            Spoiler vertex that invoked creating the summarize edge. This
	 *            is the spoiler vertex that used the corresponding return edge.
	 */
	private void addSummarizeEdge(final SpoilerDoubleDeckerVertex<LETTER, STATE> src,
			final SpoilerDoubleDeckerVertex<LETTER, STATE> dest,
			final SpoilerDoubleDeckerVertex<LETTER, STATE> spoilerInvoker) {
		// Only add if not already existent
		if (m_SrcDestToSummarizeEdges.get(src, dest) == null) {
			SummarizeEdge<LETTER, STATE> summarizeEdge = new SummarizeEdge<>(src, dest, spoilerInvoker);
			m_SrcDestToSummarizeEdges.put(src, dest, summarizeEdge);

			DuplicatorVertex<LETTER, STATE> entryShadowVertex = summarizeEdge.getEntryShadowVertex();
			SpoilerVertex<LETTER, STATE> middleShadowVertex = summarizeEdge.getMiddleShadowVertex();
			DuplicatorVertex<LETTER, STATE> exitShadowVertex = summarizeEdge.getExitShadowVertex();

			// Add shadow vertices
			addDuplicatorVertex(entryShadowVertex);
			addSpoilerVertex(middleShadowVertex);
			addDuplicatorVertex(exitShadowVertex);

			// Add edges connecting source and destination with shadow vertices
			m_GameGraph.addEdge(summarizeEdge.getSource(), entryShadowVertex);
			m_GameGraph.addEdge(entryShadowVertex, middleShadowVertex);
			m_GameGraph.addEdge(middleShadowVertex, exitShadowVertex);
			m_GameGraph.addEdge(exitShadowVertex, summarizeEdge.getDestination());

			m_SimulationPerformance.increaseCountingMeasure(ECountingMeasure.SUMMARIZE_EDGES);
		}
	}

	/**
	 * Applies all possible down state configurations to a given vertex that
	 * specifies the up states.
	 * 
	 * @param vertex
	 *            Vertex to add configurations to
	 */
	private void applyVertexDownStatesToVertex(final DuplicatorDoubleDeckerVertex<LETTER, STATE> vertex) {
		Iterator<VertexDownState<STATE>> vertexDownStatesIter = constructAllVertexDownStates(vertex.getQ0(),
				vertex.getQ1());
		while (vertexDownStatesIter.hasNext()) {
			vertex.addVertexDownState(vertexDownStatesIter.next());
		}
	}

	/**
	 * Applies all possible down state configurations to a given vertex that
	 * specifies the up states.
	 * 
	 * @param vertex
	 *            Vertex to add configurations to
	 */
	private void applyVertexDownStatesToVertex(final SpoilerDoubleDeckerVertex<LETTER, STATE> vertex) {
		Iterator<VertexDownState<STATE>> vertexDownStatesIter = constructAllVertexDownStates(vertex.getQ0(),
				vertex.getQ1());
		while (vertexDownStatesIter.hasNext()) {
			vertex.addVertexDownState(vertexDownStatesIter.next());
		}
	}

	/**
	 * Calculates the priority of a given {@link SpoilerVertex} by its
	 * representation <i>(state spoiler is at, state duplicator is at)</i>.<br/>
	 * Note that {@link DuplicatorVertex} objects always should have priority 2.
	 * 
	 * @param leftState
	 *            The state spoiler is at
	 * @param rightState
	 *            The state duplicator is at
	 * @return The calculated priority of the given {@link SpoilerVertex} which
	 *         is 0 if the right state is final, 2 if both are final and 1 if
	 *         only the left state is final.
	 */
	private int calculatePriority(final STATE leftState, final STATE rightState) {
		// In direct simulation, every vertex has zero as priority
		if (m_SimulationType == ESimulationType.DIRECT) {
			return 0;
		}

		// In delayed simulation priority zero is always possible, only priority
		// one is conditional. In this case, this method should only return one
		// if possible, else zero.
		if (m_SimulationType == ESimulationType.DELAYED) {
			if (!m_Nwa.isFinal(rightState)) {
				return 1;
			} else {
				return 0;
			}
		}

		if (m_Nwa.isFinal(rightState)) {
			return 0;
		} else if (m_Nwa.isFinal(leftState)) {
			return 1;
		} else {
			return 2;
		}
	}

	/**
	 * Tries to cast the game graph to a fair game graph and returns it.
	 * 
	 * @return The graph casted to a fair game graph, <tt>null</tt> if not
	 *         possible.
	 */
	private FairGameGraph<LETTER, STATE> castGraphToFairGameGraph() {
		FairGameGraph<LETTER, STATE> fairGraph = null;
		if (m_GameGraph instanceof FairGameGraph<?, ?>) {
			fairGraph = (FairGameGraph<LETTER, STATE>) m_GameGraph;
		}
		return fairGraph;
	}

	/**
	 * Creates an iterator over all possible vertex down states for two given up
	 * states.
	 * 
	 * @param leftUpState
	 *            The left up state to combine its down states
	 * @param rightUpState
	 *            The right up state to combine its down states
	 * @return Iterator over all possible vertex down states for two given up
	 *         states
	 */
	private Iterator<VertexDownState<STATE>> constructAllVertexDownStates(final STATE leftUpState,
			final STATE rightUpState) {
		Set<STATE> leftDownStates = m_Nwa.getDownStates(leftUpState);
		Set<STATE> rightDownStates = m_Nwa.getDownStates(rightUpState);
		Set<VertexDownState<STATE>> vertexDownStates = new LinkedHashSet<>();
		for (STATE leftDownState : leftDownStates) {
			for (STATE rightDownState : rightDownStates) {
				vertexDownStates.add(new VertexDownState<>(leftDownState, rightDownState));
			}
		}
		return vertexDownStates.iterator();
	}

	/**
	 * Returns whether Duplicator would directly loose in direct simulation if
	 * moving to the given Spoiler vertex, or if Spoiler moves from here to him.
	 * This is the case if Spoilers left state is final and the right state is
	 * not.
	 * 
	 * @param leftSpoilerState
	 *            Left state of Spoilers vertex
	 * @param rightSpoilerState
	 *            Right state of Spoilers vertex
	 * @return Whether Duplicator would directly loose in direct simulation if
	 *         moving to the given Spoiler vertex, or if Spoiler moves from here
	 *         to him.
	 */
	private boolean doesLooseInDirectSim(final STATE leftSpoilerState, final STATE rightSpoilerState) {
		boolean doesLoose = m_Nwa.isFinal(leftSpoilerState) && !m_Nwa.isFinal(rightSpoilerState);
		if (doesLoose) {
			m_Logger.debug("\t\tDuplicator directly looses with Spoiler in: (" + leftSpoilerState + ", "
					+ rightSpoilerState + ")");
		}
		return doesLoose;
	}

	/**
	 * Gets the amount of {@link SpoilerVertex} objects that exist in the game
	 * graph with representation (q0, q1). Since there can be such vertices with
	 * the extra bit false and true the returned value is between zero and two.
	 * 
	 * @param q0
	 *            The state spoiler is at
	 * @param q1
	 *            The state duplicator is at
	 * @return The amount of {@link SpoilerVertex} objects that exist in the
	 *         game graph with representation (q0, q1). Since there can be such
	 *         vertices with the extra bit false and true the returned value is
	 *         between zero and two.
	 */
	private int getAmountOfBitsForSpoilerVertices(final STATE q0, final STATE q1) {
		int amount = 0;

		if (getSpoilerVertex(q0, q1, false, null, null) != null) {
			amount++;
		}

		if (getSpoilerVertex(q0, q1, true, null, null) != null) {
			amount++;
		}

		return amount;
	}

	/**
	 * Returns if a given up state has a given down state.
	 * 
	 * @param upState
	 *            Up state in question
	 * @param downState
	 *            Down state in question
	 * @return If the given up state has the given down state.
	 */
	private boolean hasDownState(final STATE upState, final STATE downState) {
		return m_Nwa.getDownStates(upState).contains(downState);
	}

	/**
	 * Increases the internal counter of the amount of result states by one.
	 */
	private void increaseResultAmountOfStates() {
		m_ResultAmountOfStates++;
	}

	/**
	 * Increases the internal counter of the amount of result transitions by
	 * one.
	 */
	private void increaseResultAmountOfTransitions() {
		m_ResultAmountOfTransitions++;
	}

	/**
	 * Generates an equivalence class for the given state from the nwa
	 * automaton, if fair simulation.
	 * 
	 * @param leftState
	 *            State to make equivalence class for
	 */
	private void makeEquivalenceClass(final STATE leftState) {
		FairGameGraph<LETTER, STATE> fairGraph = castGraphToFairGameGraph();
		if (fairGraph != null) {
			fairGraph.getEquivalenceClasses().makeEquivalenceClass(leftState);
		}
	}

	/**
	 * Updates the priority of the summarize edge corresponding to the given
	 * objects, if the current down state is safe.
	 * 
	 * @param invoker
	 *            Element corresponding to the duplicator vertex that uses the
	 *            call which invoked the summarize edge
	 * @param priorityToSet
	 *            Priority to set for the summarize edge
	 */
	private void updateCorrespondingSummarizeEdge(final SearchElement<LETTER, STATE> invoker, int priorityToSet) {
		// We need to compute which summarize edges correspond to the current
		// vertex.
		// We do so by using the to the summarize edge corresponding down state
		// configuration. This is exactly the down state the current
		// configuration leads to after using the outgoing call edge.
		// We access this by using the history element of the search element.
		Vertex<LETTER, STATE> invokingVertex = invoker.getVertex();
		VertexDownState<STATE> historyDownState = invoker.getHistory();
		VertexDownState<STATE> invokingDownState = invoker.getDownState();
		// The corresponding down state defines the source of the corresponding
		// edges. If the down state is [q0, q1] then all corresponding summarize
		// edges have (q0, q1) as source.
		int bound = 1;
		// In delayed simulation there may be up to two sources, differentiating
		// in the bit, depending on if they are predecessors of the invoker.
		if (m_SimulationType == ESimulationType.DELAYED) {
			bound = 2;
		}
		for (int i = 0; i < bound; i++) {
			// First use the false bit. In other cases also try the true bit.
			boolean bitToUse = i != 0;

			Vertex<LETTER, STATE> sourceOfSummarizeEdges = getSpoilerVertex(historyDownState.getLeftDownState(),
					historyDownState.getRightDownState(), bitToUse, null, null);
			if (sourceOfSummarizeEdges != null && sourceOfSummarizeEdges instanceof SpoilerDoubleDeckerVertex<?, ?>) {
				SpoilerDoubleDeckerVertex<LETTER, STATE> sourceOfSummarizeEdgeAsSpoilerDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) sourceOfSummarizeEdges;
				// First we need to validate if the invoking down state forms a
				// safe down state.
				// If the down state is unsafe we do not update summarize edges.
				// We do so by first assuming that the down state is reversely
				// safe, that is when following outgoing edges to the search
				// root. The down state then is safe if the computed
				// source of the summarize edges is a predecessor
				// of the current vertex.
				if (!(m_GameGraph.hasPredecessors(invokingVertex)
						&& m_GameGraph.getPredecessors(invokingVertex).contains(sourceOfSummarizeEdges))) {
					m_Logger.debug("\t\tIs no pred: " + sourceOfSummarizeEdges + ", for: " + invokingVertex);
					return;
				}
				// Additionally the down state of the current vertex must be
				// receivable by using the call transition with any down state
				// of the summarize edge source vertex.
				// Search for a corresponding down state to validate safeness of
				// the invoking down state.
				boolean foundCorrespondingDownState = false;
				for (VertexDownState<STATE> sourceDownState : sourceOfSummarizeEdgeAsSpoilerDD.getVertexDownStates()) {
					// The right down states must be equal, also the left down
					// state must change to the called state.
					if (sourceDownState.getRightDownState().equals(invokingDownState.getRightDownState())
							&& invokingDownState.getLeftDownState().equals(sourceOfSummarizeEdges.getQ0())) {
						foundCorrespondingDownState = true;
						break;
					}
				}
				if (!foundCorrespondingDownState) {
					m_Logger.debug("\t\tFound no state in: " + sourceOfSummarizeEdgeAsSpoilerDD + ", for: "
							+ invokingDownState);
					return;
				}

				// Down state is safe, now update the priority of all
				// corresponding summarize edges
				Map<SpoilerDoubleDeckerVertex<LETTER, STATE>, SummarizeEdge<LETTER, STATE>> destToEdges = m_SrcDestToSummarizeEdges
						.get(sourceOfSummarizeEdgeAsSpoilerDD);
				if (destToEdges != null) {
					for (SummarizeEdge<LETTER, STATE> summarizeEdge : destToEdges.values()) {
						summarizeEdge.setPriority(priorityToSet);
						m_Logger.debug("\t\tUpdated summarize edge: " + summarizeEdge.hashCode());
					}
				}
			}
		}
	}

	/**
	 * Adds a given duplicator vertex to the graph and all corresponding
	 * internal fields.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		// In direct simulation, every duplicator vertex has a priority
		// of zero, we need to ensure that.
		if (m_SimulationType == ESimulationType.DIRECT) {
			vertex.setPriority(0);
		}

		if (vertex instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
			DuplicatorDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) vertex;
			m_GameGraph.getInternalDuplicatorVerticesField().add(vertexAsDD);
			m_AutomatonStatesToGraphDuplicatorVertex.put(
					new Hep<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.getLetter(), vertexAsDD.isB(),
							vertexAsDD.getTransitionType(), vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()),
					vertexAsDD);
		} else {
			m_GameGraph.addDuplicatorVertex(vertex);
		}
	}

	/**
	 * Adds a given spoiler vertex to the graph and all corresponding internal
	 * fields.
	 * 
	 * @param vertex
	 *            Vertex to add
	 */
	protected void addSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		// In direct simulation, every spoiler vertex has a priority
		// of zero, we need to ensure that.
		if (m_SimulationType == ESimulationType.DIRECT) {
			vertex.setPriority(0);
		}

		if (vertex instanceof SpoilerDoubleDeckerVertex<?, ?>) {
			SpoilerDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) vertex;
			m_GameGraph.getInternalSpoilerVerticesField().add(vertexAsDD);
			m_AutomatonStatesToGraphSpoilerVertex.put(new Quin<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(),
					vertexAsDD.isB(), vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()), vertexAsDD);
		} else {
			m_GameGraph.addSpoilerVertex(vertex);
		}
	}

	/**
	 * Removes a given duplicator vertex from the graph and all corresponding
	 * internal fields.
	 * 
	 * @param vertex
	 *            Vertex to remove
	 */
	protected void removeDuplicatorVertex(final DuplicatorVertex<LETTER, STATE> vertex) {
		if (vertex instanceof DuplicatorDoubleDeckerVertex<?, ?>) {
			DuplicatorDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (DuplicatorDoubleDeckerVertex<LETTER, STATE>) vertex;
			m_GameGraph.getInternalDuplicatorVerticesField().remove(vertexAsDD);
			m_AutomatonStatesToGraphDuplicatorVertex
					.put(new Hep<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(), vertexAsDD.getLetter(), vertexAsDD.isB(),
							vertexAsDD.getTransitionType(), vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()), null);
		} else {
			m_GameGraph.removeDuplicatorVertex(vertex);
		}
	}

	/**
	 * Removes a given spoiler vertex from the graph and all corresponding
	 * internal fields.
	 * 
	 * @param vertex
	 *            Vertex to remove
	 */
	protected void removeSpoilerVertex(final SpoilerVertex<LETTER, STATE> vertex) {
		if (vertex instanceof SpoilerDoubleDeckerVertex<?, ?>) {
			SpoilerDoubleDeckerVertex<LETTER, STATE> vertexAsDD = (SpoilerDoubleDeckerVertex<LETTER, STATE>) vertex;
			m_GameGraph.getInternalSpoilerVerticesField().remove(vertexAsDD);
			m_AutomatonStatesToGraphSpoilerVertex.put(new Quin<>(vertexAsDD.getQ0(), vertexAsDD.getQ1(),
					vertexAsDD.isB(), vertexAsDD.getSummarizeEdge(), vertexAsDD.getSink()), null);
		} else {
			m_GameGraph.removeSpoilerVertex(vertex);
		}
	}
}
