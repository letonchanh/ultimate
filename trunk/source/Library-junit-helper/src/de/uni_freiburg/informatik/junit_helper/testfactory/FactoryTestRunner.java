/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE JUnit Helper Library.
 * 
 * The ULTIMATE JUnit Helper Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE JUnit Helper Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE JUnit Helper Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE JUnit Helper Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE JUnit Helper Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.junit_helper.testfactory;

import static org.junit.Assert.fail;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.junit.runners.BlockJUnit4ClassRunner;
import org.junit.runners.model.FrameworkMethod;
import org.junit.runners.model.InitializationError;
import org.junit.runners.model.TestClass;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class FactoryTestRunner extends BlockJUnit4ClassRunner {

	private List<FrameworkMethod> mTests;
	private final String mTestSuiteName;

	public FactoryTestRunner(Class<?> claaas) throws InitializationError {
		super(claaas);
		mTestSuiteName = claaas.getSimpleName();
	}

	protected Collection<? extends FrameworkMethod> generateFactoryTests() {
		List<FrameworkFactoryTest> tests = new ArrayList<FrameworkFactoryTest>();
		TestClass classUnderTest = getTestClass();

		// create an instance of the current class
		Object currentInstance = null;
		try {
			currentInstance = classUnderTest.getOnlyConstructor().newInstance();
		} catch (Exception e1) {
			e1.printStackTrace();
			return tests;
		}

		// Find all methods in the current class marked with @TestFactory.
		for (final FrameworkMethod method : classUnderTest.getAnnotatedMethods(TestFactory.class)) {

			// Execute the current @TestFactory method
			Object factoryMethod;
			try {
				factoryMethod = method.getMethod().invoke(currentInstance);
			} catch (InvocationTargetException ex) {
				System.err.println("Exception during invocation of test method:");
				final Throwable cause = ex.getCause();
				if (cause != null) {
					cause.printStackTrace();
				}
				continue;
			} catch (Exception e) {
				e.printStackTrace();
				continue;
			}

			if (factoryMethod.getClass().isArray()) {
				// Did the factory return an array? If so, make it a list.
				factoryMethod = Arrays.asList((Object[]) factoryMethod);
			}

			if (!(factoryMethod instanceof Iterable<?>)) {
				// Did the factory return a single object? If so, put it in a
				// list.
				factoryMethod = Collections.singletonList(factoryMethod);
			}

			// For each object returned by the factory.
			for (Object instance : (Iterable<?>) factoryMethod) {
				// Find any methods marked with @FactoryTest and add them to the
				// return list

				for (FrameworkMethod m : new TestClass(instance.getClass())
						.getAnnotatedMethods(FactoryTestMethod.class)) {
					tests.add(new FrameworkFactoryTest(m.getMethod(), instance, instance.toString()));
				}
			}
		}
		return tests;
	}

	/**
	 * {@inheritDoc}
	 * 
	 * @see org.junit.runners.BlockJUnit4ClassRunner#computeTestMethods()
	 */
	@Override
	protected List<FrameworkMethod> computeTestMethods() {
		if (mTests == null) {
			mTests = new ArrayList<FrameworkMethod>();
		}
		if (mTests.isEmpty()) {
			// generateFactoryTests collects all tests from invoking methods
			// that
			// are marked with @TestFactory
			mTests.addAll(generateFactoryTests());

			if (mTests.isEmpty()) {
				// ok, so no factory tests were generated; in this case, we add
				// our own factory test that will a) always fail and b) report
				// to the user that no dynamic test was generated and that this
				// is failure
				try {
					final String errorMsg = getTestClass().getName() + " did not return any dynamic tests";
					mTests.add(new FrameworkFactoryTest(FailingTest.class.getMethod("NoFactoryTestMethod"),
							new FailingTest(), errorMsg));
				} catch (Exception e) {
					// this reflection is always safe
				}

			}

			// computeTestMethods returns all methods that are marked with @Test
			mTests.addAll(super.computeTestMethods());
		}
		return mTests;
	}

	@Override
	protected String getName() {
		return mTestSuiteName;
	}
	
	public class FailingTest {
		public void NoFactoryTestMethod() {
			fail("TestSuite run with custom runner FactoryTestRunner must return at least one dynamic generated test through their @TestFactory methods");
		}
	}
}
