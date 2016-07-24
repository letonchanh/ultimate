/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.boogie.IProgramVar;
import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.SilentReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa.NWAPathProgramTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLibraryModeResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.PointerExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.RCFGArrayIndexCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Should be used by other tools to run abstract interpretation on various parts of the RCFG.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class AbstractInterpreter {

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 * Suppress all exceptions except {@link OutOfMemoryError}, {@link ToolchainCanceledException},
	 * {@link IllegalArgumentException}. Produce no results.
	 * 
	 */
	@SuppressWarnings("squid:S1166")
	public static IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ProgramPoint> runSilently(final RootNode root,
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services) {
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			return run(root, initials, timer, services, true);
		} catch (final OutOfMemoryError oom) {
			throw oom;
		} catch (final IllegalArgumentException iae) {
			throw iae;
		} catch (final ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			return null;
		} catch (final Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getMessage());
			return null;
		}
	}

	/**
	 * Run abstract interpretation on a path program constructed from a counterexample.
	 * 
	 */
	@SuppressWarnings("squid:S1166")
	public static IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> runOnPathProgram(
			final NestedRun<CodeBlock, ?> counterexample,
			final INestedWordAutomatonOldApi<CodeBlock, ?> currentAutomata, final RootNode root,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) {
		assert counterexample != null && counterexample.getLength() > 0 : "Invalid counterexample";
		assert currentAutomata != null;
		assert root != null;
		assert services != null;
		assert timer != null;

		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			final NWAPathProgramTransitionProvider transProvider =
					new NWAPathProgramTransitionProvider(counterexample, services, root.getRootAnnot());
			return runSilentlyOnNWA(transProvider, counterexample.getSymbol(0), root, timer, services);
		} catch (final ToolchainCanceledException tce) {
			// suppress timeout results / timeouts
			logger.warn("Abstract interpretation run out of time");
			return null;
		}
	}

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 */
	public static IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, ProgramPoint> run(final RootNode root,
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services, final boolean isSilent) throws Throwable {
		if (initials == null) {
			throw new IllegalArgumentException("No initial edges provided");
		}
		if (timer == null) {
			throw new IllegalArgumentException("timer is null");
		}

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final Script script = rootAnnot.getScript();
		final Boogie2SmtSymbolTable boogieVarTable = bpl2smt.getBoogie2SmtSymbolTable();
		final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider = new RcfgTransitionProvider();
		final ILoopDetector<CodeBlock> loopDetector =
				new RcfgLoopDetector<>(rootAnnot.getLoopLocations().keySet(), transitionProvider);

		final IAbstractDomain<?, CodeBlock, IBoogieVar, Expression> domain =
				selectDomain(root, () -> new RCFGLiteralCollector(root), symbolTable, services, rootAnnot);

		return run(initials, timer, services, symbolTable, bpl2smt, script, boogieVarTable, loopDetector, domain,
				transitionProvider, rootAnnot, isSilent);
	}

	private static AbstractInterpretationResult<?, CodeBlock, IBoogieVar, ?> runSilentlyOnNWA(
			final NWAPathProgramTransitionProvider transProvider, final CodeBlock initial, final RootNode root,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) {

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final Script script = rootAnnot.getScript();
		final Boogie2SmtSymbolTable boogieVarTable = bpl2smt.getBoogie2SmtSymbolTable();

		final IAbstractDomain<?, CodeBlock, IBoogieVar, Expression> domain =
				selectDomain(root, () -> new RCFGLiteralCollector(root), symbolTable, services, rootAnnot);

		return runSilentlyOnNWA(initial, timer, services, symbolTable, bpl2smt, script, boogieVarTable, domain,
				transProvider, transProvider, rootAnnot);
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock>, LOC>
			AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, LOC> runSilentlyOnNWA(final CodeBlock initial,
					final IProgressAwareTimer timer, final IUltimateServiceProvider services,
					final BoogieSymbolTable symbolTable, final Boogie2SMT bpl2smt, final Script script,
					final Boogie2SmtSymbolTable boogieVarTable,
					final IAbstractDomain<STATE, CodeBlock, IBoogieVar, Expression> domain,
					final ITransitionProvider<CodeBlock, LOC> transitionProvider,
					final ILoopDetector<CodeBlock> loopDetector, final RootAnnot rootAnnot) {

		final RcfgDebugHelper<STATE, LOC> debugHelper = new RcfgDebugHelper<STATE, LOC>(rootAnnot, services);
		final FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, LOC, Expression> params =
				new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, LOC, Expression>(services).setDomain(domain)
						.setLoopDetector(loopDetector)
						.setStorage(new RcfgAbstractStateStorageProvider<STATE, LOC>(domain.getMergeOperator(),
								services, transitionProvider))
						.setTransitionProvider(transitionProvider)
						.setVariableProvider(new RcfgVariableProvider<>(symbolTable, boogieVarTable, services))
						.setDebugHelper(debugHelper).setTimer(timer);

		final FixpointEngine<STATE, CodeBlock, IBoogieVar, LOC, Expression> fxpe = new FixpointEngine<>(params);
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		try {
			final AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, LOC> result =
					fxpe.run(initial, script, bpl2smt);
			if (!result.hasReachedError()) {
				logger.info("NWA was safe (error state unreachable)");
			} else {
				logger.info("Could not show that NWA was safe (error state reachable)");
			}
			if (logger.isDebugEnabled()) {
				logger.debug("Found the following predicates:");
				AbsIntUtil.logPredicates(Collections.singletonMap(initial, result.getLoc2Term()), script,
						logger::debug);
			}
			logger.info(result.getBenchmark());
			return result;
		} catch (final ToolchainCanceledException c) {
			throw c;
		}
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock>>
			AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, ProgramPoint>
			run(final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
					final IUltimateServiceProvider services, final BoogieSymbolTable symbolTable,
					final Boogie2SMT bpl2smt, final Script script, final Boogie2SmtSymbolTable boogieVarTable,
					final ILoopDetector<CodeBlock> loopDetector,
					final IAbstractDomain<STATE, CodeBlock, IBoogieVar, Expression> domain,
					final ITransitionProvider<CodeBlock, ProgramPoint> transitionProvider, final RootAnnot rootAnnot,
					final boolean isSilent) {
		final Collection<CodeBlock> filteredInitialElements = transitionProvider.filterInitialElements(initials);

		if (filteredInitialElements.isEmpty()) {
			getReporter(services, false, false).reportSafe(null, "The program is empty");
			return null;
		}

		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final boolean isLib = filteredInitialElements.size() > 1;

		final Iterator<CodeBlock> iter = filteredInitialElements.iterator();
		AbstractInterpretationResult<STATE, CodeBlock, IBoogieVar, ProgramPoint> result = null;
		// TODO: If an if is at the beginning of a method, this method will be analyzed two times
		while (iter.hasNext()) {
			final CodeBlock initial = iter.next();

			final FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression> params =
					new FixpointEngineParameters<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression>(services)
							.setDomain(domain).setLoopDetector(loopDetector)
							.setStorage(new RcfgAbstractStateStorageProvider<STATE, ProgramPoint>(
									domain.getMergeOperator(), services, transitionProvider))
							.setTransitionProvider(transitionProvider)
							.setVariableProvider(new RcfgVariableProvider<>(symbolTable, boogieVarTable, services))
							.setDebugHelper(new RcfgDebugHelper<>(rootAnnot, services)).setTimer(timer);

			final FixpointEngine<STATE, CodeBlock, IBoogieVar, ProgramPoint, Expression> fxpe =
					new FixpointEngine<>(params);
			result = fxpe.run(initial, script, bpl2smt, result);
		}
		if (result == null) {
			logger.error("Could not run because no initial element could be found");
			return null;
		}
		if (result.hasReachedError()) {
			final IResultReporter<STATE, CodeBlock, IBoogieVar, ProgramPoint> reporter =
					getReporter(services, isLib, isSilent);
			result.getCounterexamples().forEach(cex -> reporter.reportPossibleError(cex));
		} else {
			getReporter(services, false, isSilent).reportSafe(null);
		}
		if (logger.isDebugEnabled()) {
			logger.debug("Found the following predicates:");
			AbsIntUtil.logPredicates(result.getLoc2Term(), logger::debug);
		}
		logger.info(result.getBenchmark());
		return result;
	}

	private static BoogieSymbolTable getSymbolTable(final RootNode root) {
		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			return null;
		}
		return pa.getSymbolTable();
	}

	private static IAbstractDomain<?, CodeBlock, IBoogieVar, Expression> selectDomain(RootNode root,
			final LiteralCollectorFactory literalCollector, final BoogieSymbolTable symbolTable,
			final IUltimateServiceProvider services, final RootAnnot rootAnnotation) {
		final IPreferenceProvider prefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		// use the literal collector result if you need it
		// new LiteralCollector(root).getResult();

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(services, rootAnnotation, symbolTable);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(logger, symbolTable, literalCollector.create().getLiteralCollection(), services,
					rootAnnotation);
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			return new OctagonDomain(logger, symbolTable, literalCollector, services, rootAnnotation);
		} else if (VPDomain.class.getSimpleName().equals(selectedDomain)) {
			final RCFGArrayIndexCollector arrayIndexCollector = new RCFGArrayIndexCollector(root);
			if (logger.isDebugEnabled()) {
				printVPDomainDebug(logger, arrayIndexCollector);
			}
			return new VPDomain(services, arrayIndexCollector.getPointerMap(),
					arrayIndexCollector.getIndexToArraysMap(), rootAnnotation);
		} else if (CongruenceDomain.class.getSimpleName().equals(selectedDomain)) {
			return new CongruenceDomain(logger, services, symbolTable, rootAnnotation);
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			@SuppressWarnings("rawtypes")
			final List<IAbstractDomain> domainList = new ArrayList<>();
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
				domainList.add(new EmptyDomain<>());
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
				domainList.add(new SignDomain(services, rootAnnotation, symbolTable));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
				domainList.add(new CongruenceDomain(logger, services, symbolTable, rootAnnotation));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
				domainList.add(new IntervalDomain(logger, symbolTable, literalCollector.create().getLiteralCollection(),
						services, rootAnnotation));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
				domainList.add(new OctagonDomain(logger, symbolTable, literalCollector, services, rootAnnotation));
			}
			return new CompoundDomain(services, domainList, rootAnnotation);
		}
		throw new UnsupportedOperationException("The value \"" + selectedDomain + "\" of preference \""
				+ AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN + "\" was not considered before! ");
	}

	private static void printVPDomainDebug(final ILogger logger, final RCFGArrayIndexCollector arrayIndexCollector) {
		for (final Entry<IProgramVar, Set<PointerExpression>> bv : arrayIndexCollector.getPointerMap().entrySet()) {
			logger.debug("PointerMap Key: " + bv.getKey());
			for (final PointerExpression val : bv.getValue()) {
				logger.debug("PointerMap Value: " + val.toString());
			}
		}
		logger.debug("============");
		for (final Entry<IProgramVar, Set<IProgramVar>> bv : arrayIndexCollector.getIndexToArraysMap().entrySet()) {
			logger.debug("IndexToArraysMap Key: " + bv.getKey());
			for (final IProgramVar val : bv.getValue()) {
				logger.debug("IndexToArraysMap Value: " + val);
			}
		}
	}

	private static <STATE extends IAbstractState<STATE, CodeBlock>, VARDECL>
			IResultReporter<STATE, CodeBlock, VARDECL, ProgramPoint>
			getReporter(final IUltimateServiceProvider services, final boolean isLibrary, final boolean isSilent) {
		if (isSilent) {
			return new SilentReporter<>();
		}
		if (isLibrary) {
			return new RcfgLibraryModeResultReporter<STATE, VARDECL>(services);
		} else {
			return new RcfgResultReporter<STATE, VARDECL>(services);
		}
	}

	@FunctionalInterface
	public interface LiteralCollectorFactory {
		RCFGLiteralCollector create();
	}
}
