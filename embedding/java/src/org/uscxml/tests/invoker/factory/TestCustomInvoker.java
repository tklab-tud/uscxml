package org.uscxml.tests.invoker.factory;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InvokeRequest;
import org.uscxml.Invoker;
import org.uscxml.SendRequest;
import org.uscxml.StringList;

public class TestCustomInvoker extends Invoker {

	@Override
	public StringList getNames() {
		StringList ss = new StringList();
		ss.add("java");
		return ss;
	}

	@Override
	public Data getDataModelVariables() {
		Data data = new Data();
		return data;
	}

	@Override
	public void send(SendRequest req) {
		System.out.println(req);
		if ("foo".equals(req.getName()))
			returnEvent(new Event("received2")); // enqueue an external event
	}

	@Override
	public void invoke(InvokeRequest req) {
		System.out.println(req);
		if ("Some string content".equals(req.getContent())) {
			returnEvent(new Event("received1")); // enqueue an external event
		}
	}

	@Override
	public void uninvoke() {
		System.out.println("uninvoke");
	}

	@Override
	public Invoker create(Interpreter interpreter) {
		TestCustomInvoker invoker = new TestCustomInvoker();
		invoker.swigReleaseOwnership();
		return invoker;
	}

	/**
	 * @param args
	 * @throws InterpreterException 
	 */
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		TestCustomInvoker invoker = new TestCustomInvoker();
		// just register prototype at global factory
		Factory.getInstance().registerInvoker(invoker);

		String xml = 
		"<scxml>" +
		"  <state id=\"s1\">" +
		"    <invoke type=\"java\" id=\"javainvoker1\">" +
		"    	<content>Some string content</content>" +
		"    </invoke>" +
		"    <invoke type=\"java\" id=\"javainvoker2\" />" +
		"    <state id=\"s11\">" +
		"    	<transition event=\"received1\" target=\"s12\" />" +		
		"    </state>" +
		"    <state id=\"s12\">" +
		"		<onentry>" +
        "           <log label=\"label\" expr=\"foo\" />" +
		"			<send target=\"#_javainvoker2\" event=\"foo\" />" +
		"		</onentry>" +
		"    	<transition event=\"received2\" target=\"done\" />" +		
		"    </state>" +
		"  </state>" +
		"  <final id=\"done\" />" +
		"</scxml>";

		// parse and interpret
		Interpreter interpreter = Interpreter.fromXML(xml, "");
		interpreter.interpret();
	}

}
