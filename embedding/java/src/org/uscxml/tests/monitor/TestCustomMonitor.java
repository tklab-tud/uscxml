package org.uscxml.tests.monitor;

import org.uscxml.Data;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterMonitor;

public class TestCustomMonitor extends InterpreterMonitor {

	@Override
	public void afterEnteringState(Interpreter interpreter, String stateId,
			String xpath, String state, boolean moreComing) {
		System.out.println("Entered state " + stateId);
		if ("s2".equals(stateId)) {
			Data data = interpreter.getDataModel().getStringAsData("foo");
			System.out.println(data);
		}
	}

	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		String xml = 
		"<scxml datamodel=\"ecmascript\">" +
		"  <datamodel>" +
		"    <data id=\"foo\">" + 
		"      { foo: 'bar', baz: 'foo' }" +
		"    </data>" + 
		"  </datamodel>" +
		"  <state id=\"s1\">" +
		"    <transition target=\"s2\" />" +
		"  </state>" +
		"  <state id=\"s2\">" +
		"    <transition target=\"s3\" />" +
		"  </state>" +
		"  <state id=\"s3\">" +
		"    <transition target=\"done\" />" +
		"  </state>" +
		"  <final id=\"done\" />" +
		"</scxml>";

		// parse and interpret
		Interpreter interpreter = Interpreter.fromXML(xml, "");
		
		TestCustomMonitor monitor = new TestCustomMonitor();
		interpreter.addMonitor(monitor);
		
		interpreter.interpret();
	}

}
