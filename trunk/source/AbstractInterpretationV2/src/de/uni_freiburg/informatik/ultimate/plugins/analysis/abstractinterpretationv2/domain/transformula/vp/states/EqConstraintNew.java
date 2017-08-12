package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;

public class EqConstraintNew {

	ThreeValuedEquivalenceRelation<E>
}

abstract class EqTerm {
	
	private Term mTerm;

	EqTerm(Term term) {
		mTerm = term;
	}

	Term getTerm() {
		return mTerm;
	}
	
	abstract EqTerm rename(Map<Term, Term> renaming);	
}

abstract class EqElementTerm extends EqTerm {
	
}

class EqSelectTerm extends EqElementTerm {
	
}

class EqAtomicTerm extends EqElementTerm {

}

class EqNonAtomicTerm extends EqElementTerm {

}

class EqArrayTerm extends EqTerm {
	
}