package org.uscxml.apache.commons.scxml2;

import java.net.URL;

import org.uscxml.ActionLanguage;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;
import org.uscxml.helper.TestMonitor;

public class SCXMLExecutor {

	public Interpreter interpreter = null;
	public URL sourceURL = null;
	public ActionLanguage al = new ActionLanguage();
	
	public SCXMLExecutor(Evaluator evaluator, Object object, SimpleErrorReporter simpleErrorReporter) {
		// TODO Auto-generated constructor stub
	}

	public void setStateMachine(SCXML scxml) {
		sourceURL = scxml.url;
	}

	public void setRootContext(Context rootContext) {
		al.setDataModel(rootContext.dm);
	}

	public void go() {
		try {
			interpreter = Interpreter.fromURL(sourceURL.toString());
			interpreter.setActionLanguage(al);
			
			TestMonitor tm = new TestMonitor();
			interpreter.addMonitor(tm);

			InterpreterState state = InterpreterState.USCXML_UNDEF;
			while(state != InterpreterState.USCXML_FINISHED) {
				interpreter.step();
			}
			
		} catch (InterpreterException e) {
			e.printStackTrace();
		}
		
	}

}
