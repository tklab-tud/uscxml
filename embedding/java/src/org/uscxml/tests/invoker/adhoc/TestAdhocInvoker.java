package org.uscxml.tests.invoker.adhoc;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InvokeRequest;
import org.uscxml.Invoker;
import org.uscxml.SendRequest;
import org.uscxml.StringList;

public class TestAdhocInvoker extends Invoker {

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
			returnEvent(new Event("received2"), true); // enqueue an external event
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

	/**
	 * @param args
	 * @throws InterpreterException 
	 */
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

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

		TestAdhocInvoker javainvoker1 = new TestAdhocInvoker();
		TestAdhocInvoker javainvoker2 = new TestAdhocInvoker();

		// parse and interpret
		Interpreter interpreter = Interpreter.fromXML(xml);
		interpreter.setInvoker("javainvoker1", javainvoker1);
		interpreter.setInvoker("javainvoker2", javainvoker2);
		interpreter.interpret();
		
	}

}
