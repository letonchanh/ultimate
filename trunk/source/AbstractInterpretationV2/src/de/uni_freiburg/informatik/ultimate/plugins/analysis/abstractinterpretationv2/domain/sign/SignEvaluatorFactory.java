package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Factory for evaluators of the sign domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignEvaluatorFactory implements IEvaluatorFactory<Values, CodeBlock, BoogieVar> {

	private static final int ARITY_MIN = 1;
	private static final int ARITY_MAX = 2;
	private static final int BUFFER_MAX = 100;

	private final SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final IUltimateServiceProvider mServices;

	/**
	 * Creates a new evaluator factory for the sign domain.
	 * 
	 * @param services
	 *            The Ultimate services.
	 * @param stateConverter
	 *            The state converter in the sign domain.
	 */
	public SignEvaluatorFactory(IUltimateServiceProvider services,
	        SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mStateConverter = stateConverter;
		mServices = services;
	}

	@Override
	public INAryEvaluator<Values, CodeBlock, BoogieVar> createNAryExpressionEvaluator(int arity) {

		assert arity >= ARITY_MIN && arity <= ARITY_MAX;

		switch (arity) {
		case ARITY_MIN:
			return new SignUnaryExpressionEvaluator();
		case ARITY_MAX:
			return new SignBinaryExpressionEvaluator(mServices);
		default:
			final StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("Arity of ").append(arity).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());
		}
	}

	@Override
	public IEvaluator<Values, CodeBlock, BoogieVar> createSingletonValueExpressionEvaluator(String value,
	        Class<?> valueType) {

		if (valueType.equals(BigInteger.class)) {
			return new SignSingletonIntegerExpressionEvaluator(value);
		}

		if (valueType.equals(BigDecimal.class)) {
			return new SignSingletonDecimalExpressionEvaluator(value);
		}

		throw new UnsupportedOperationException("The type " + valueType.toString() + " is not supported.");
	}

	@Override
	public IEvaluator<Values, CodeBlock, BoogieVar> createSingletonVariableExpressionEvaluator(String variableName) {
		return new SignSingletonVariableExpressionEvaluator(variableName, mStateConverter);
	}
}
