/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE WitnessParser plug-in.
 * 
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;

public class WitnessNodeAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;
	private static final String sKey = Activator.s_PLUGIN_ID + "_Node";
	private static final String[] sFieldNames = new String[] { "IsInitial", "IsError", "IsSink", "Invariant" };

	private final boolean mIsInitial;
	private final boolean mIsError;
	private final boolean mIsSink;
	private final String mInvariant;

	public WitnessNodeAnnotation(final boolean isInitial, final boolean isError, final boolean isSink,
			final String invariant) {
		mIsInitial = isInitial;
		mIsError = isError;
		mIsSink = isSink;
		mInvariant = invariant;
	}

	public String getInvariant() {
		return mInvariant;
	}

	public boolean isInitial() {
		return mIsInitial;
	}

	public boolean isError() {
		return mIsError;
	}

	public boolean isSink() {
		return mIsSink;
	}

	public boolean isDefault() {
		return !mIsInitial && !mIsError && !mIsSink && mInvariant == null;
	}

	@Override
	protected String[] getFieldNames() {
		return sFieldNames;
	}

	@Override
	protected Object getFieldValue(final String field) {
		switch (field) {
		case "IsInitial":
			return mIsInitial;
		case "IsError":
			return mIsError;
		case "IsSink":
			return mIsSink;
		case "Invariant":
			return mInvariant;
		}
		return null;
	}

	public void annotate(IElement node) {
		if (node instanceof WitnessNode) {
			annotate((WitnessNode) node);
		}
	}

	public void annotate(WitnessNode node) {
		node.getPayload().getAnnotations().put(sKey, this);
	}

	public static WitnessNodeAnnotation getAnnotation(IElement node) {
		if (node instanceof WitnessNode) {
			getAnnotation((WitnessNode) node);
		}
		return null;
	}

	public static WitnessNodeAnnotation getAnnotation(WitnessNode node) {
		if (node.hasPayload()) {
			IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				IAnnotations annot = payload.getAnnotations().get(sKey);
				if (annot != null) {
					return (WitnessNodeAnnotation) annot;
				}
			}
		}
		return null;
	}
}
