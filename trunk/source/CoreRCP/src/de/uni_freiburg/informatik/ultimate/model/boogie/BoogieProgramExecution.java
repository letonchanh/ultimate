package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IValuation;
import de.uni_freiburg.informatik.ultimate.result.ResultUtil;

public class BoogieProgramExecution implements IProgramExecution<BoogieASTNode, Expression> {

	private final List<BoogieASTNode> m_Trace;
	private final Map<Integer, ProgramState<Expression>> m_PartialProgramStateMapping;

	public BoogieProgramExecution(List<BoogieASTNode> trace,
			Map<Integer, ProgramState<Expression>> partialProgramStateMapping) {
		super();
		m_Trace = trace;
		m_PartialProgramStateMapping = partialProgramStateMapping;
	}

	@Override
	public int getLength() {
		return m_Trace.size();
	}

	@Override
	public BoogieASTNode getTraceElement(int i) {
		return m_Trace.get(i);
	}

	@Override
	public ProgramState<Expression> getProgramState(int i) {
		if (i < 0 || i >= m_Trace.size()) {
			throw new IllegalArgumentException("out of range");
		}
		return m_PartialProgramStateMapping.get(i);
	}

	@Override
	public ProgramState<Expression> getInitialProgramState() {
		return m_PartialProgramStateMapping.get(-1);
	}

	private String ppstoString(ProgramState<Expression> pps) {
		String result;
		if (pps == null) {
			result = null;
		} else {
			List<Expression> keys = new ArrayList<>(pps.getVariables());
			Collections.sort(keys, new Comparator<Expression>() {
				@Override
				public int compare(Expression arg0, Expression arg1) {
					return BoogiePrettyPrinter.print(arg0).compareToIgnoreCase(BoogiePrettyPrinter.print(arg1));
				}
			});

			StringBuilder sb = new StringBuilder();
			for (Expression variable : keys) {
				Expression value = pps.getValues(variable).iterator().next();
				sb.append("  ");
				String var = BoogiePrettyPrinter.print(variable);
				String val = BoogiePrettyPrinter.print(value);
				sb.append(var + "=" + val);
			}
			result = sb.toString();
		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String valuation = ppstoString(getInitialProgramState());
		String lineSeparator = System.getProperty("line.separator");
		if (valuation != null) {
			sb.append("initial values:");
			sb.append(valuation);
			sb.append(lineSeparator);
		}
		for (int i = 0; i < m_Trace.size(); i++) {
			sb.append("statement");
			sb.append(i);
			sb.append(": ");
			if (m_Trace.get(i) instanceof Statement) {
				sb.append(BoogiePrettyPrinter.print((Statement) m_Trace.get(i)));
			} else {
				sb.append(m_Trace.get(i));
			}
			sb.append(lineSeparator);
			valuation = ppstoString(getProgramState(i));
			if (valuation != null) {
				sb.append("values");
				sb.append(i);
				sb.append(":");
				sb.append(valuation);
				sb.append(lineSeparator);
			}
		}
		return sb.toString();
	}

	public IValuation getValuation(final List<ITranslator<?, ?, ?, ?>> translatorSequence) {
		return new IValuation() {
			@Override
			public Map<String, SimpleEntry<IType, List<String>>> getValuesForFailurePathIndex(int index) {
				ProgramState<Expression> ps = getProgramState(index);
				if (ps == null) {
					return getEmtpyProgramState();
				} else {
					return translateProgramState(ps);
				}
			}

			public Map<String, SimpleEntry<IType, List<String>>> getEmtpyProgramState() {
				return Collections.emptyMap();
			}

			public Map<String, SimpleEntry<IType, List<String>>> translateProgramState(ProgramState<Expression> ps) {
				Map<String, SimpleEntry<IType, List<String>>> result = new HashMap<String, SimpleEntry<IType, List<String>>>();
				for (Expression var : ps.getVariables()) {
					String varString = ResultUtil.backtranslationWorkaround(translatorSequence, var);
					List<String> valuesString = exprSet2StringList(ps.getValues(var));
					result.put(varString, new SimpleEntry<IType, List<String>>(var.getType(), valuesString));
				}
				return result;
			}

			private List<String> exprSet2StringList(Collection<Expression> expressions) {
				List<String> result = new ArrayList<String>(expressions.size());
				for (Expression expr : expressions) {
					result.add(ResultUtil.backtranslationWorkaround(translatorSequence, expr));
				}
				return result;
			}
		};
	}

	@Override
	public Class<Expression> getExpressionClass() {
		return Expression.class;
	}

	@Override
	public Class<BoogieASTNode> getTraceElementClass() {
		return BoogieASTNode.class;
	}
}
