/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Provides auxiliary methods for SMT bitvectors.
 * @author Matthias Heizmann
 *
 */
public class BitvectorUtils {
	
	private enum SupportedBitvectorOperations { 
		zero_extend,
		extract,
		bvadd,
		bvsub,
		bvmul,
		bvudiv,
		bvurem,
		bvsdiv,
		bvsrem,
		bvand,
		bvor,
		bvxor,
		bvnot,
		bvneg,
		bvshl,
		bvlshr,
		bvashr,
		bvult,
		bvule,
		bvugt,
		bvuge,
		bvslt,
		bvsle,
		bvsgt,
		bvsge,
	}
	private BitvectorUtils() {
		// Prevent instantiation of this utility class
	}
	
	private final static String BITVEC_CONST_PATTERN = "bv\\d+";
	
	public static boolean isBitvectorConstant(FunctionSymbol symb) {
		return symb.isIntern() && symb.getName().matches(BITVEC_CONST_PATTERN);
	}
	
	public static boolean isBitvectorSort(Sort sort) {
		return sort.getRealSort().getName().equals("BitVec");
	}
	
	/**
	 * Convert term to {@link BitvectorConstant} object.
	 * Return a {@link BitvectorConstant} object for term if 
	 * @param term
	 * @return {@link BitvectorConstant} object that represents term if term
	 * is a bitvector literal otherwise null is returned.
	 */
	public static BitvectorConstant constructBitvectorConstant(Term term) {
		if (term instanceof ApplicationTerm) {
			if (term.getSort().getName().equals("BitVec")) {
				if (term.getSort().getIndices().length == 1) {
					ApplicationTerm appTerm = (ApplicationTerm) term;
					FunctionSymbol symb = appTerm.getFunction();
					if (isBitvectorConstant(symb)) {
						assert (symb.getName().startsWith("bv"));
						String valueString = symb.getName().substring(2);
						BigInteger value = new BigInteger(valueString);
						BigInteger index = term.getSort().getIndices()[0];
						return new BitvectorConstant(value, index);
					}
				}
			}
		}
		return null;
	}

	/**
	 * @return Term that represents bitvector (value % 2^index)
	 */
	public static Term constructTerm(Script script, BigInteger value, Sort sort) {
		BigInteger index = sort.getIndices()[0];
		return constructTerm(script, new BitvectorConstant(value, index));
	}
	
	public static Term constructTerm(Script script, BitvectorConstant bitvec) {
		String funcname = "bv" + bitvec.getValue().toString();
		return script.term(funcname, new BigInteger[]{bitvec.getIndex()}, null, new Term[0]);
	}
	
	public static boolean allTermsAreBitvectorConstants(Term[] terms) {
		for (Term term : terms) {
			if (!term.getSort().getName().equals("BitVec")) {
				return false;
			} else {
				if (term instanceof ApplicationTerm) {
					ApplicationTerm appTerm = (ApplicationTerm) term;
					if (isBitvectorConstant(appTerm.getFunction())) {
						continue;
					} else {
						return false;
					}
				} else {
					return false;
				}
			}
		}
		return true;
	}
	
	public static Term termWithLocalSimplification(Script script, 
			String funcname, BigInteger[] indices, Term... params) {
		final Term result;
		SupportedBitvectorOperations bvop = SupportedBitvectorOperations.valueOf(funcname);
		switch (bvop) {
		case zero_extend:
			result = new Zero_extend().simplifiedResult(script, funcname, indices, params);
			break;
		case extract:
			result = new Extract().simplifiedResult(script, funcname, indices, params);
			break;
		case bvadd:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvadd(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvsub:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsub(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvudiv:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvudiv(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvurem:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvurem(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvsdiv:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsdiv(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvsrem:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvsrem(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvmul:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvmul(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvand:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvand(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvor:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvor(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvxor:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvxor(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvnot:
			result = new Bvnot().simplifiedResult(script, funcname, indices, params);
			break;
		case bvneg:
			result = new Bvneg().simplifiedResult(script, funcname, indices, params);
			break;
		case bvshl:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvshl(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvlshr:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvlshr(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvashr:
			result = new RegularBitvectorOperation_BitvectorResult(funcname, x -> y -> BitvectorConstant.bvashr(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvult:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvult(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvule:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvule(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvugt:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvugt(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvuge:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvuge(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvslt:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvslt(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvsle:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvsle(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvsgt:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvsgt(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;
		case bvsge:
			result = new RegularBitvectorOperation_BooleanResult(funcname, x -> y -> BitvectorConstant.bvsge(x, y)).
			simplifiedResult(script, funcname, indices, params);
			break;

		default:
			if (BitvectorUtils.allTermsAreBitvectorConstants(params)) {
				throw new AssertionError("wasted optimization " + funcname);
			}
			result = script.term(funcname, indices, null, params);
			break;
		}
		return result;
	}
	
	
	private static abstract class BitvectorOperation {
		
		public final Term simplifiedResult(Script script, String funcname, BigInteger[] indices, Term... params) {
			assert getFunctionName().equals(funcname) : "wrong function name";
			assert getNumberOfIndices() == 0 && indices == null || getNumberOfIndices() == indices.length : "wrong number of indices";
			assert getNumberOfParams() == params.length : "wrong number of params";
			BitvectorConstant[] bvs = new BitvectorConstant[params.length];
			boolean allConstant = true;
			for (int i=0; i<params.length; i++) {
				bvs[i] = constructBitvectorConstant(params[i]);
				allConstant &= (bvs[i] != null);
			}
			if (allConstant) {
				return simplify_ConstantCase(script, indices, bvs);
			} else {
				return simplify_NonConstantCase(script, indices, params, bvs); 
			}
		}
		
		private Term simplify_NonConstantCase(Script script, BigInteger[] indices, Term[] params,
				BitvectorConstant[] bvs) {
			return notSimplified(script, indices, params);
		}

		private final Term notSimplified(Script script, BigInteger[] indices, Term[] params) {
			return script.term(getFunctionName(), indices, null, params);
		}

		public abstract String getFunctionName();
		public abstract int getNumberOfIndices();
		public abstract int getNumberOfParams();
		
		public abstract Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs);
	}
	
	private static class Extract extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "extract";
		}

		@Override
		public int getNumberOfIndices() {
			return 2;
		}

		@Override
		public int getNumberOfParams() {
			return 1;
		}

		@Override
		public Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs) {
			BitvectorConstant bv = BitvectorConstant.extract(bvs[0], indices[0].intValueExact(), indices[1].intValueExact());
			return constructTerm(script, bv);
		}
		
	}
	
	private static class Zero_extend extends BitvectorOperation {

		@Override
		public String getFunctionName() {
			return "zero_extend";
		}

		@Override
		public int getNumberOfIndices() {
			return 1;
		}

		@Override
		public int getNumberOfParams() {
			return 1;
		}

		@Override
		public Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs) {
			BitvectorConstant bv = BitvectorConstant.zero_extend(bvs[0], indices[0]);
			return constructTerm(script, bv);
		}
		
	}

	private static abstract class RegularBitvectorOperation extends BitvectorOperation {
		

		@Override
		public int getNumberOfIndices() {
			return 0;
		}

		@Override
		public int getNumberOfParams() {
			return 2;
		}
		
	}
	
	private static class RegularBitvectorOperation_BitvectorResult extends RegularBitvectorOperation {
		
		private final String m_Name;
		private final Function<BitvectorConstant, Function<BitvectorConstant, BitvectorConstant>> m_Function;
		public RegularBitvectorOperation_BitvectorResult(String name,
				Function<BitvectorConstant, Function<BitvectorConstant, BitvectorConstant>> function) {
			super();
			m_Name = name;
			m_Function = function;
		}
		@Override
		public String getFunctionName() {
			return m_Name;
		}
		@Override
		public Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs) {
			return constructTerm(script, m_Function.apply(bvs[0]).apply(bvs[1]));
		}
	}
	
	private static class RegularBitvectorOperation_BooleanResult extends RegularBitvectorOperation {
		
		private final String m_Name;
		private final Function<BitvectorConstant, Function<BitvectorConstant, Boolean>> m_Function;
		public RegularBitvectorOperation_BooleanResult(String name,
				Function<BitvectorConstant, Function<BitvectorConstant, Boolean>> function) {
			super();
			m_Name = name;
			m_Function = function;
		}
		@Override
		public String getFunctionName() {
			return m_Name;
		}
		@Override
		public Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs) {
			return script.term(String.valueOf(m_Function.apply(bvs[0]).apply(bvs[1])));
		}
	}
	
	private static class Bvnot extends BitvectorOperation {
		@Override
		public String getFunctionName() { return "bvnot"; }
		@Override
		public int getNumberOfIndices() {
			return 0;
		}
		@Override
		public int getNumberOfParams() {
			return 1;
		}
		@Override
		public Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs) {
			return constructTerm(script, BitvectorConstant.bvnot(bvs[0]));
		}

	}
	
	private static class Bvneg extends BitvectorOperation {
		@Override
		public String getFunctionName() { return "bvneg"; }
		@Override
		public int getNumberOfIndices() {
			return 0;
		}
		@Override
		public int getNumberOfParams() {
			return 1;
		}
		@Override
		public Term simplify_ConstantCase(Script script, BigInteger[] indices, BitvectorConstant[] bvs) {
			return constructTerm(script, BitvectorConstant.bvneg(bvs[0]));
		}

	}

}
