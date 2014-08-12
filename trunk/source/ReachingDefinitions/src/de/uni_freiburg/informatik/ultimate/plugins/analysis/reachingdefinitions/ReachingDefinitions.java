package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions;

import java.util.Collections;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.IAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefEdgeAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefGraphAnnotationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations.ReachDefStatementAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.rcfg.ReachDefRCFG;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.trace.ReachDefTrace;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class ReachingDefinitions implements IAnalysis {

	private GraphType mCurrentGraphType;
	private IUltimateServiceProvider mServices;

	@Override
	public GraphType getOutputDefinition() {
		return mCurrentGraphType;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		mCurrentGraphType = graphType;
	}

	@Override
	public List<IObserver> getObservers() {
		if (mCurrentGraphType.getCreator().equals(
				de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator.PLUGIN_ID)) {
			IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider = new ReachDefGraphAnnotationProvider<>(null);
			IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider = new ReachDefGraphAnnotationProvider<>(null);
			Logger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
			return Collections.singletonList((IObserver) new ReachDefRCFG(logger, stmtProvider, edgeProvider));
		}
		return Collections.emptyList();
	}

	@Override
	public int init() {
		return 0;
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	public static CodeBlock[] computeRDForTrace(CodeBlock[] trace, Logger logger) throws Throwable {
		// TODO: Der neue Plan
		// - Forest bauen, jedes assume ist eine Wurzel (nach hinten)
		// - assume macht use und def
		// - ...?
		IAnnotationProvider<ReachDefEdgeAnnotation> edgeProvider = new ReachDefGraphAnnotationProvider<>(null);
		IAnnotationProvider<ReachDefStatementAnnotation> stmtProvider = new ReachDefGraphAnnotationProvider<>(null);
		ReachDefTrace rdt = new ReachDefTrace(edgeProvider, stmtProvider, logger);
		rdt.process(trace);
		return trace;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {

	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
	}

}
