package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

class LassoConstructor<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final GeneralizedNestedWordAutomatonReachableStates<LETTER, STATE> mReach;
	private NestedRun<LETTER, STATE> mLoop;
	private NestedRun<LETTER, STATE> mStem;
	private StateContainer<LETTER, STATE> mGoal;
	private final NestedLassoRun<LETTER, STATE> mLasso;
	private final List<STATE> mSCC;
	private final Set<STATE> mSCCSet;
	
	LassoConstructor(final AutomataLibraryServices services,
			final GeneralizedNestedWordAutomatonReachableStates<LETTER, STATE> reach
			, final List<STATE> sccList) throws AutomataOperationCanceledException {
		mServices = services;
		mReach = reach;
		mSCC = sccList;
		mSCCSet = new HashSet<>(mSCC.size());
		for(STATE state : mSCC) {
			mSCCSet.add(state);
		}
		constructStemRun();
		constructLoopRun();
		mLasso = new NestedLassoRun<>(mStem, mLoop);
	}
	
	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
		return mLasso;
	}
	
	private void constructLoopRun() throws AutomataOperationCanceledException {
		// we know that the root is the last state in the list
		LinkedList<STATE> newList = new LinkedList<>();
		boolean preInsertion = true;
		for(STATE current : mSCC) {
			if(preInsertion) {
				newList.addFirst(current);
			}else {
				newList.addLast(current);
			}
			if(current.equals(mGoal.getState())) {
				preInsertion = false;
			}
		}
		assert newList.getFirst().equals(mGoal.getState());
		mLoop = new NestedRun<>(mGoal.getState());
		
		// goal -> d1 -> d2 -> d3 -> ... -> dn
		newList.removeFirst();
		StateContainer<LETTER, STATE> stateCont = mGoal;
		Set<Integer> labels = new HashSet<>();
		labels.addAll(mReach.getAcceptanceLabels(stateCont.getState()));
		STATE backState = null;
		for(STATE current : newList) {
			testTimeoutCancelException(this.getClass());
			LETTER letter = stateCont.getLetterOfSuccessor(current);
			NestedRun<LETTER, STATE> newSuffix;
			if(letter != null) {
				// path exists
				labels.addAll(mReach.getAcceptanceLabels(current));
				newSuffix = new NestedRun<>(stateCont.getState(), letter, NestedWord.INTERNAL_POSITION,
						current);
			}else {
				// no direct transition to current, so find shortest one
				final Set<STATE> source = new HashSet<>();
				final Set<STATE> target = new HashSet<>();
				source.add(stateCont.getState());
				target.add(current);
				RunConstructor rc = new RunConstructor(source, target, true);
				newSuffix = rc.getNestedRun();
				labels.addAll(rc.getLabels());
			}
			mLoop = mLoop.concatenate(newSuffix);
			backState = current;
			if(labels.size() == mReach.getAcceptanceSize()) {
				break;
			}
			stateCont = mReach.getStateContainer(current);
		}
		assert labels.size() == mReach.getAcceptanceSize();
		final Set<STATE> source = new HashSet<>();
		final Set<STATE> target = new HashSet<>();
		source.add(backState);
		target.add(mGoal.getState());
		RunConstructor rc = new RunConstructor(source, target, true);
		NestedRun<LETTER, STATE> newSuffix = rc.getNestedRun();
		mLoop = mLoop.concatenate(newSuffix);
	}
	

	private void constructStemRun() throws AutomataOperationCanceledException {
		// construct a run from initial state to mGoal
		RunConstructor rc = new RunConstructor(mReach.getInitialStates(), mSCCSet, false);
		mStem = rc.getNestedRun();
		mGoal = mReach.getStateContainer(mStem.getStateAtPosition(mStem.getLength()-1));
		assert mSCCSet.contains(mGoal.getState());
	}

	
	private void testTimeoutCancelException(Class<?> clazz) throws AutomataOperationCanceledException {
		if (mServices.getProgressAwareTimer() != null 
		     && !mServices.getProgressAwareTimer().continueProcessing()) {
			throw new AutomataOperationCanceledException(clazz);
		}
	}
	
	// ------------ 
	private class SuccessorInfo{
		final STATE mState;
		int mDistance;
		STATE mPredState;
		LETTER mLetter;
		SuccessorInfo(STATE state) {
			mState = state;
			mPredState = null;
			mLetter = null;
			mDistance = Integer.MAX_VALUE;
		}
		
		@Override
		public boolean equals(Object obj) {
			if(this == obj) return true;
			if(!(obj instanceof LassoConstructor.SuccessorInfo)) {
				return false;
			}
			@SuppressWarnings("unchecked")
			SuccessorInfo otherInfo = (SuccessorInfo)obj;
			return mState.equals(otherInfo.mState);
		}
		
		@Override
		public String toString() {
			return "<" + mState + "," + mDistance + "," + mPredState + "," + mLetter + ">";
		}
	}
	
	private class ComparatorSuccessorInfo implements Comparator<SuccessorInfo> {
		@Override
		public int compare(LassoConstructor<LETTER, STATE>.SuccessorInfo fstSuccInfo,
				LassoConstructor<LETTER, STATE>.SuccessorInfo sndSuccInfo) {
			return fstSuccInfo.mDistance - sndSuccInfo.mDistance;
		}
	}
	
	/**
	 * We assume that there must be a run from some state in mSources
	 * to some state in mTargets
	 * */
	private class RunConstructor {
		
		private final Set<STATE> mSources;
		private final Set<STATE> mTargets;
		private NestedRun<LETTER, STATE> mNestedRun;
		private final Map<STATE, SuccessorInfo> mSuccInfo = new HashMap<>();
		private STATE mFoundState;
		private Set<Integer> mLabels;
		private boolean mIsLoop;
		
		RunConstructor(Set<STATE> sources, Set<STATE> targets, boolean isLoop) {
			mSources = sources;
			mTargets = targets;
			mIsLoop = isLoop;
			if(mIsLoop) {
				mLabels = new HashSet<>();
			}
		}
		
		NestedRun<LETTER, STATE> getNestedRun() throws AutomataOperationCanceledException {
			if(mNestedRun == null) {
				breathFirstSearch();
				constructRunBackwards();
			}
			return mNestedRun;
		}
		
		Set<Integer> getLabels() {
			return mLabels;
		}

		private SuccessorInfo getSuccessorInfoPrivate(STATE succ) {
			SuccessorInfo succInfo = mSuccInfo.get(succ);
			if(succInfo == null) {
				succInfo = new SuccessorInfo(succ);
				mSuccInfo.put(succ, succInfo);
			}
			return succInfo;
		}
		
		private void constructRunBackwards() throws AutomataOperationCanceledException {
			SuccessorInfo currInfo = mSuccInfo.get(mFoundState);
			if(currInfo == null) return ;
			mNestedRun = new NestedRun<>(mFoundState);
			if(mIsLoop) {
				mLabels.addAll(mReach.getAcceptanceLabels(mFoundState));
			}
			while(! mSources.contains(currInfo.mState)) {
				testTimeoutCancelException(this.getClass());
				// current state is the first state in the stem
				assert currInfo.mState.equals(mNestedRun.getStateAtPosition(0));
				NestedRun<LETTER, STATE> newPrefix = new NestedRun<>(
						currInfo.mPredState, currInfo.mLetter
					, NestedWord.INTERNAL_POSITION, currInfo.mState);
				mNestedRun = newPrefix.concatenate(mNestedRun);
				currInfo = mSuccInfo.get(currInfo.mPredState);
				if(mIsLoop) {
					mLabels.addAll(mReach.getAcceptanceLabels(currInfo.mState));
				}
			}
		}
		
		private void breathFirstSearch() throws AutomataOperationCanceledException {
			// construct a run from initial state to mGoal
			PriorityQueue<SuccessorInfo> queue = new PriorityQueue<>(new ComparatorSuccessorInfo());
			
			// initialize sources
			for (STATE state : mSources) {
				SuccessorInfo succInfo = getSuccessorInfoPrivate(state);
				succInfo.mDistance = 0; // zero distance to mGoal
				queue.add(succInfo);
			}

			Set<STATE> visited = new HashSet<>();
			while (! queue.isEmpty()) {
				testTimeoutCancelException(this.getClass());
				// current state
				SuccessorInfo currInfo = queue.remove();
				if (visited.contains(currInfo))
					continue;
				if (mTargets.contains(currInfo.mState)) {
					// already found shortest path
					mFoundState = currInfo.mState;
					break;
				}
				if(currInfo.mDistance == Integer.MAX_VALUE) {
					assert false : "Target not reachable";
					break;
				}
				visited.add(currInfo.mState);
				StateContainer<LETTER, STATE> stateCont = mReach.getStateContainer(currInfo.mState);
				for (OutgoingInternalTransition<LETTER, STATE> trans : stateCont.internalSuccessors()) {
					testTimeoutCancelException(this.getClass());
					int dis = currInfo.mDistance + 1;
					SuccessorInfo succInfo = getSuccessorInfoPrivate(trans.getSucc());
					if (succInfo.mDistance > dis && !visited.contains(trans.getSucc())) {
						// value become smaller
						succInfo.mDistance = dis;
						succInfo.mLetter = trans.getLetter();
						succInfo.mPredState = currInfo.mState;
						// update the priority of succInfo
						queue.remove(succInfo);
						queue.add(succInfo);
					}
				}
			}
		}
		
		
	}
	

}