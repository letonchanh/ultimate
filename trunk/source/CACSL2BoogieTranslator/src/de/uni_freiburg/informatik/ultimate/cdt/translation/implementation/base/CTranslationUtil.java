/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Provides utility methods for the C to Boogie translation.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CTranslationUtil {

	private CTranslationUtil() {
		// don't instantiate this utility class
	}

	public static AuxVarHelper makeAuxVarDeclaration(final ILocation loc, final Dispatcher main, final CType cType) {
		final AUXVAR auxVarType;
		if (cType instanceof CArray) {
			auxVarType = SFO.AUXVAR.ARRAYINIT;
		} else if (cType instanceof CStruct) {
			auxVarType = SFO.AUXVAR.STRUCTINIT;
		} else {
			throw new UnsupportedOperationException();
		}
		return makeAuxVarDeclaration(loc, main, cType, auxVarType);
	}

	public static AuxVarHelper makeAuxVarDeclaration(final ILocation loc, final Dispatcher main, final CType cType,
					final AUXVAR auxVarType) {
		final String id = main.mNameHandler.getTempVarUID(auxVarType, cType);
		final VariableDeclaration decl = new VariableDeclaration(loc,
				new Attribute[0],
				new VarList[] {
						new VarList(loc, new String[] { id }, main.mTypeHandler.cType2AstType(loc, cType)) });

		final VariableLHS lhs = new VariableLHS(loc, id);

		final IdentifierExpression exp = new IdentifierExpression(loc, id);

		return new AuxVarHelper(decl, lhs, exp);
	}

	public static LocalLValue constructArrayAccessLhs(final ILocation loc, final LocalLValue arrayLhsToInitialize,
			final List<Integer> arrayIndex, final AExpressionTranslation expressionTranslation) {
		final CArray cArrayType = (CArray) arrayLhsToInitialize.getCType().getUnderlyingType();

		assert cArrayType.getDimensions().length == arrayIndex.size();

		final Expression[] index = new Expression[arrayIndex.size()];
		for (int i = 0; i < arrayIndex.size(); i++) {
			final CPrimitive currentIndexType = (CPrimitive) cArrayType.getDimensions()[i].getCType();
			index[i] = expressionTranslation.constructLiteralForIntegerType(loc, currentIndexType,
					new BigInteger(arrayIndex.get(i).toString()));
		}

		final ArrayLHS alhs = ExpressionFactory.constructArrayLhs(loc, arrayLhsToInitialize.getLHS(), index);

		return new LocalLValue(alhs, cArrayType.getValueType());
	}

	public static LRValue constructOffHeapStructAccessLhs(final ILocation loc, final LocalLValue structBaseLhs,
			final int i) {
		final CStruct cStructType = (CStruct) structBaseLhs.getCType().getUnderlyingType();
		final String fieldName = cStructType.getFieldIds()[i];
		final StructLHS lhs = ExpressionFactory.constructStructAccessLhs(loc, structBaseLhs.getLHS(), fieldName);
		return new LocalLValue(lhs, cStructType.getFieldTypes()[i]);
	}

//	public static HeapLValue constructOnHeapStructAccessLhs(final HeapLValue structBaseLhs, final int i) {
//		final CStruct cStructType = (CStruct) structBaseLhs.getCType();
//		// TODO
//		return null;
//	}

	public static HeapLValue constructAddressForArrayAtIndex(final ILocation loc, final Dispatcher main,
			final HeapLValue arrayBaseAddress, final List<Integer> arrayIndex) {
		final CArray cArrayType = (CArray) arrayBaseAddress.getCType();

		final List<Integer> arrayBounds = getConstantDimensionsOfArray(cArrayType);

		Integer product = 0;
		for (int i = 0; i < arrayIndex.size(); i++) {
			final int factor = i == arrayIndex.size() - 1 ? 1 : arrayBounds.get(i + 1);
			product = product +  factor * arrayIndex.get(i);
		}
		final CPrimitive sizeT = main.mCHandler.getTypeSizeAndOffsetComputer().getSizeT();

		final Expression flatCellNumber = main.mCHandler.getExpressionTranslation()
				.constructLiteralForIntegerType(loc, sizeT, new BigInteger(product.toString()));

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(arrayBaseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(arrayBaseAddress.getAddress(), loc);
		final Expression cellOffset = main.mCHandler.getMemoryHandler().multiplyWithSizeOfAnotherType(loc,
				cArrayType.getValueType(), flatCellNumber, sizeT);
		final Expression sum = main.mCHandler.getExpressionTranslation().constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, pointerOffset, sizeT, cellOffset, sizeT);
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);

		return new HeapLValue(newPointer, cArrayType.getValueType());
	}

//	public static HeapLValue constructAddressForStructField(final ILocation loc, final Dispatcher main,
//			final HeapLValue structBaseAddress, final int fieldNr) {
//		final CStruct cStructType = (CStruct) structBaseAddress.getCType();
//		main.mCHandler.getTypeSizeAndOffsetComputer().constructOffsetForField(loc, cStructType, fieldNr);
//		return null;
//	}


	public static HeapLValue constructAddressForStructField(final ILocation loc, final Dispatcher main,
			final HeapLValue baseAddress, final int fieldIndex) {
		final CStruct cStructType = (CStruct) baseAddress.getCType().getUnderlyingType();

		final CPrimitive sizeT = main.mCHandler.getTypeSizeAndOffsetComputer().getSizeT();

		final Expression fieldOffset = main.mCHandler.getTypeSizeAndOffsetComputer().constructOffsetForField(
						loc, cStructType, fieldIndex);
//		final HeapLValue fieldPointer = new HeapLValue(fieldAddress, cStructType.getFieldTypes()[i]);


		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(baseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(baseAddress.getAddress(), loc);
//		final Expression cellOffset = main.mCHandler.getMemoryHandler().multiplyWithSizeOfAnotherType(loc,
//				cArrayType.getValueType(), flatCellNumber, sizeT);
		final Expression sum = main.mCHandler.getExpressionTranslation().constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, pointerOffset, sizeT, fieldOffset, sizeT);
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);


		return new HeapLValue(newPointer, cStructType.getFieldTypes()[fieldIndex]);
	}

	public static boolean isVarlengthArray(final CArray cArrayType) {
		for (final RValue dimRVal : cArrayType.getDimensions()) {
			if (!(dimRVal.getValue() instanceof IntegerLiteral)) {
				return true;
			}
		}
		return false;
	}


	public static List<Integer> getConstantDimensionsOfArray(final CArray cArrayType) {
		if (CTranslationUtil.isVarlengthArray(cArrayType)) {
			throw new IllegalArgumentException("only call this for non-varlength array types");
		}
		final List<Integer> result = new ArrayList<>();
		for (final RValue dimRVal : cArrayType.getDimensions()) {
			final int dimInt = Integer.parseUnsignedInt(((IntegerLiteral) dimRVal.getValue()).getValue());
			result.add(dimInt);
		}
		return result;
	}

	public static boolean isAggregateType(final CType valueType) {
		return valueType instanceof CStruct || valueType instanceof CArray;
	}

}