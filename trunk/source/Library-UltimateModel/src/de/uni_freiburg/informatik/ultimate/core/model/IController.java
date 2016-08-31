/*
 * Copyright (C) 2007-2015 Christian Ortolf
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model;

import java.util.Collection;
import java.util.List;

/**
 * This is the interface that all plugins providing a user interface to Ultimate should implement. UltimateCore should
 * always use methods in this interface, and if necessary, extend it to request user interaction.
 *
 * @author dietsch
 * @param <T>
 *            The type of toolchain this controller supports
 *
 */
public interface IController<T> extends IUltimatePlugin {

	/**
	 * {@link UltimateCore} initializes a controller during startup with this callback. This call delegates control to
	 * the controller.
	 *
	 * @param core
	 *            The active {@link UltimateCore} instance that can be used by the controller to start various Ultimate
	 *            functions.
	 * @return A status code that determines whether the IController instance completed successfully or not. Use 0 to
	 *         signal normal termination.
	 */
	int init(ICore<T> core);

	/**
	 * Here the controller tells the caller what parser to use. Usually, the core will try to determine that
	 * automatically. This should only be called if that is not possible and hence the user's opinion is needed.
	 *
	 * @param parser
	 *            providing parsers
	 * @return what parser should be used null if the toolchain should be interrupted
	 */
	ISource selectParser(Collection<ISource> parser);

	/**
	 * Here the controller tells the caller what toolchain to use.
	 *
	 * @param tools
	 *            available tools
	 * @return the desired toolchain as instance of Toolchain
	 */
	IToolchainData<T> selectTools(List<ITool> tools);

	/**
	 * Here the controller tells the caller (usually the core) what model out of a set of model ids the user has chosen.
	 *
	 * @param modelNames
	 * @return string with model id
	 */
	List<String> selectModel(List<String> modelNames);

	/**
	 * Should be called to notify the user that the toolchain proved the program to be incorrect
	 */
	void displayToolchainResultProgramIncorrect();

	/**
	 * Should be called to notify the user that the toolchain proved the program to be correct
	 */
	void displayToolchainResultProgramCorrect();

	/**
	 * Should be called to notify the user that the toolchain failed to prove the program correct or incorrect for some
	 * reason.
	 *
	 * @param description
	 *            The reason why the result of the analysis is unknown.
	 */
	void displayToolchainResultProgramUnknown(final String description);

	/**
	 * Is called by the core if the controller should display an exception to the user
	 *
	 * @param description
	 *            A message to the user saying why or where the exception occurred.
	 * @param ex
	 *            The exception itself.
	 */
	void displayException(String description, Throwable ex);

}
