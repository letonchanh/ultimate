package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructType;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieProgramExecution;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.GenericResult;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.result.IResultWithSeverity.Severity;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class BoogiePreprocessorBacktranslator extends
		DefaultTranslator<BoogieASTNode, BoogieASTNode, Expression, Expression> {

	private final Logger mLogger;
	/**
	 * Mapping from target nodes to source nodes (i.e. output to input)
	 */
	private final HashMap<BoogieASTNode, BoogieASTNode> mMapping;
	private final IUltimateServiceProvider mServices;
	private BoogieSymbolTable mSymbolTable;

	protected BoogiePreprocessorBacktranslator(IUltimateServiceProvider services) {
		super(BoogieASTNode.class, BoogieASTNode.class, Expression.class, Expression.class);
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mMapping = new HashMap<>();
	}

	public BoogieSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public void setSymbolTable(BoogieSymbolTable symbolTable) {
		mSymbolTable = symbolTable;
	}

	protected void addMapping(BoogieASTNode inputNode, BoogieASTNode outputNode) {
		BoogieASTNode realInputNode = mMapping.get(inputNode);
		if (realInputNode == null) {
			realInputNode = inputNode;
		}
		mMapping.put(outputNode, realInputNode);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Create mapping between");
			mLogger.debug("\tOutput " + printDebug(outputNode));
			mLogger.debug("\tInput  " + printDebug(realInputNode));
		}
	}

	private String printDebug(BoogieASTNode node) {
		if (node instanceof Statement) {
			return BoogiePrettyPrinter.print((Statement) node);
		}

		if (node instanceof Expression) {
			return BoogiePrettyPrinter.print((Expression) node);
		}

		if (node instanceof Procedure) {
			return BoogiePrettyPrinter.printSignature((Procedure) node);
		}

		if (node instanceof VarList) {
			return BoogiePrettyPrinter.print((VarList) node);
		}

		StringBuilder output = new StringBuilder();
		output.append(node.getClass().getSimpleName());
		ILocation loc = node.getLocation();

		if (loc != null) {
			int start = loc.getStartLine();
			int end = loc.getEndLine();

			output.append(" L");
			output.append(start);
			if (start != end) {
				output.append(":");
				output.append(end);
			}

			int startC = loc.getStartColumn();
			int endC = loc.getEndColumn();
			output.append(" C");
			output.append(startC);

			if (startC != endC) {
				output.append(":");
				output.append(endC);
			}
		}
		return output.toString();
	}

	@Override
	public IProgramExecution<BoogieASTNode, Expression> translateProgramExecution(
			IProgramExecution<BoogieASTNode, Expression> programExecution) {

		List<BoogieASTNode> newTrace = new ArrayList<>();
		Map<Integer, ProgramState<Expression>> newPartialProgramStateMapping = new HashMap<>();

		int length = programExecution.getLength();
		for (int i = 0; i < length; ++i) {
			BoogieASTNode elem = programExecution.getTraceElement(i);
			BoogieASTNode newElem = mMapping.get(elem);

			if (newElem == null) {
				reportUnfinishedBacktranslation("Unfinished backtranslation: No mapping for " + elem.toString());
			} else {
				if (newElem instanceof Statement) {
					newTrace.add((Statement) newElem);
				} else {
					reportUnfinishedBacktranslation("Unfinished backtranslation: Ignored translation of "
							+ newElem.getClass().getSimpleName());
				}
			}

			ProgramState<Expression> initialState = programExecution.getInitialProgramState();
			if (initialState != null) {
				// was macht man damit?
				reportUnfinishedBacktranslation("Unfinished backtranslation: Ignored initial programstate "
						+ initialState);
			}

			ProgramState<Expression> state = programExecution.getProgramState(i);
			if (state == null) {
				newPartialProgramStateMapping.put(i, null);
			} else {
				Map<Expression, Collection<Expression>> newVariable2Values = new HashMap<>();
				for (Expression var : state.getVariables()) {
					Expression newVar = translateExpression(var);
					Collection<Expression> newValues = new ArrayList<>();
					for (Expression value : state.getValues(var)) {
						newValues.add(translateExpression(value));
					}
					newVariable2Values.put(newVar, newValues);
				}
				newPartialProgramStateMapping.put(i, new ProgramState<>(newVariable2Values));
			}
		}
		// TODO: During development, I switch these comments to have a "clean"
		// boogie translation
		// return super.translateProgramExecution(programExecution);
		return new BoogieProgramExecution(newTrace, newPartialProgramStateMapping);
	}

	@Override
	public List<BoogieASTNode> translateTrace(List<BoogieASTNode> trace) {
		// TODO Auto-generated method stub
		return super.translateTrace(trace);
	}

	@Override
	public Expression translateExpression(Expression expression) {
		return new ExpressionTranslator().processExpression(expression);
	}

	@Override
	public String targetExpressionToString(Expression expression) {
		return BoogiePrettyPrinter.print(expression);
	}

	@Override
	public List<String> targetTraceToString(List<BoogieASTNode> trace) {
		List<String> rtr = new ArrayList<>();
		for (BoogieASTNode node : trace) {
			if (node instanceof Statement) {
				rtr.add(BoogiePrettyPrinter.print((Statement) node));
			} else {
				return super.targetTraceToString(trace);
			}
		}
		return rtr;
	}

	private void reportUnfinishedBacktranslation(String message) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new GenericResult(Activator.PLUGIN_ID, "Unfinished Backtranslation", message, Severity.WARNING));
	}

	private class ExpressionTranslator extends BoogieTransformer {

		@Override
		protected Expression processExpression(Expression expr) {
			if (mSymbolTable == null) {
				reportUnfinishedBacktranslation("No symboltable available, using identity as back-translation of "
						+ expr);
				return expr;
			}

			if (expr instanceof IdentifierExpression) {
				IdentifierExpression ident = (IdentifierExpression) expr;
				if (((IdentifierExpression) expr).getDeclarationInformation() == null) {
					reportUnfinishedBacktranslation("Identifier has no declaration information, using identity as back-translation of "
							+ expr);
					return expr;
				}
				Declaration decl = mSymbolTable.getDeclaration(ident);

				if (decl == null) {
					reportUnfinishedBacktranslation("No declaration in symboltable, using identity as back-translation of "
							+ expr);
					return expr;
				}
				BoogieASTNode newDecl = mMapping.get(decl);
				if (newDecl instanceof Declaration) {
					return extractIdentifier((Declaration) newDecl, ident);
				} else {
					// this is ok
					return expr;
				}
			}
			// descend
			return super.processExpression(expr);
		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, IdentifierExpression inputExp) {
			IdentifierExpression rtr = inputExp;
			if (mappedDecl instanceof VariableDeclaration) {
				VariableDeclaration mappedVarDecl = (VariableDeclaration) mappedDecl;
				rtr = extractIdentifier(mappedVarDecl, mappedVarDecl.getVariables(), inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
				reportUnfinishedBacktranslation("Unfinished backtranslation: Name guessing unsuccessful for VarDecl "
						+ BoogiePrettyPrinter.print(mappedVarDecl) + " and expression "
						+ BoogiePrettyPrinter.print(inputExp));

			} else if (mappedDecl instanceof Procedure) {
				Procedure proc = (Procedure) mappedDecl;
				rtr = extractIdentifier(proc, proc.getInParams(), inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
				rtr = extractIdentifier(proc, proc.getOutParams(), inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
				reportUnfinishedBacktranslation("Unfinished backtranslation: Name guessing unsuccessful for Procedure "
						+ BoogiePrettyPrinter.printSignature(proc) + " and expression "
						+ BoogiePrettyPrinter.print(inputExp));
			} else {
				reportUnfinishedBacktranslation("Unfinished backtranslation: Declaration "
						+ mappedDecl.getClass().getSimpleName() + " not handled for expression "
						+ BoogiePrettyPrinter.print(inputExp));
			}

			return rtr;
		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, VarList[] list,
				IdentifierExpression inputExp) {
			if (list == null || list.length == 0) {
				return inputExp;
			}
			IdentifierExpression rtr = inputExp;
			for (VarList lil : list) {
				rtr = extractIdentifier(mappedDecl, lil, inputExp);
				if (rtr != inputExp) {
					return rtr;
				}
			}
			return rtr;
		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, VarList list,
				IdentifierExpression inputExp) {
			if (list == null) {
				return inputExp;
			}
			IType bplType = list.getType().getBoogieType();
			if (!(bplType instanceof BoogieType)) {
				throw new UnsupportedOperationException("The BoogiePreprocessorBacktranslator cannot handle "
						+ bplType.getClass().getSimpleName() + " as type of VarList");
			}
			BoogieType type = (BoogieType) bplType;
			return extractIdentifier(mappedDecl, list, inputExp, type);

		}

		private IdentifierExpression extractIdentifier(Declaration mappedDecl, VarList list,
				IdentifierExpression inputExp, BoogieType type) {
			if (type instanceof StructType) {
				StructType st = (StructType) type;
				String[] inputNames = inputExp.getIdentifier().split("\\.");
				if (inputNames.length == 1) {
					// its the struct itself
					String inputName = inputExp.getIdentifier();
					for (String name : list.getIdentifiers()) {
						if (inputName.contains(name)) {
							return new IdentifierExpression(mappedDecl.getLocation(), type, name,
									inputExp.getDeclarationInformation());
						}
					}

				} else if (inputNames.length == 2) {
					// its a struct field access
					// first, find the name of the struct
					String structName = null;
					String inputStructName = inputNames[0];
					for (String name : list.getIdentifiers()) {
						if (inputStructName.contains(name)) {
							structName = name;
							break;
						}
					}
					if (structName != null) {
						// if this worked, lets get the field name
						for (String fieldName : st.getFieldIds()) {
							if (inputNames[1].contains(fieldName)) {
								return new IdentifierExpression(mappedDecl.getLocation(), type, structName + "!"
										+ fieldName, inputExp.getDeclarationInformation());
							}
						}
					}
				} else {
					// its a nested struct field access (this sucks)
					reportUnfinishedBacktranslation("Unfinished Backtranslation: Nested struct field access of VarList "
							+ BoogiePrettyPrinter.print(list) + " not handled");
				}
			} else if (type instanceof ConstructedType) {
				ConstructedType ct = (ConstructedType) type;
				return extractIdentifier(mappedDecl, list, inputExp, ct.getUnderlyingType());
			} else if (type instanceof PrimitiveType) {
				String inputName = inputExp.getIdentifier();
				for (String name : list.getIdentifiers()) {
					if (inputName.contains(name)) {
						return new IdentifierExpression(mappedDecl.getLocation(), list.getType().getBoogieType(), name,
								inputExp.getDeclarationInformation());
					}
				}
			} else {
				reportUnfinishedBacktranslation("Unfinished Backtranslation: Type" + type + " of VarList "
						+ BoogiePrettyPrinter.print(list) + " not handled");
			}
			return inputExp;
		}
	}

}
