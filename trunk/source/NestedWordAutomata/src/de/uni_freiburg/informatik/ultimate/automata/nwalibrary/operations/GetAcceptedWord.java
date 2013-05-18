package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class GetAcceptedWord<LETTER, STATE> implements IOperation {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	NestedWord<LETTER> m_AcceptedWord;

	public GetAcceptedWord(INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		m_Operand = operand;
		s_Logger.info(startMessage());
		IsEmpty<LETTER, STATE> isEmpty = new IsEmpty<LETTER, STATE>(operand);
		if (isEmpty.getResult()) {
			throw new IllegalArgumentException(
					"unable to get word from emtpy language");
		} else {
			m_AcceptedWord = isEmpty.getNestedRun().getWord();
		}
		s_Logger.info(exitMessage());
	}

	@Override
	public NestedWord<LETTER> getResult() throws OperationCanceledException {
		return m_AcceptedWord;
	}

	@Override
	public String operationName() {
		return "getAcceptedWord";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Found word of length "
				+ m_AcceptedWord.length();
	}

}
