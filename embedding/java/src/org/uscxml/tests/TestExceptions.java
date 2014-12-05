package org.uscxml.tests;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;

public class TestExceptions {

	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");
		
		String xml =
		"<scxml datamodel=\"ecmascript\">" +
		"	<state id=\"start\">" +
		"		<transition target=\"done\" />" +
		" </state>" +
		" <final id=\"done\" />" +
		"</scxml>";

		if (false) {
			// datamodel not available before first step -> dies with segfault
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			System.out.println(interpreter.getDataModel().evalAsString("'FOO'"));
		}

		if (false) {
			// datamodel is available but syntactic ecmascript exception is not propagated
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			interpreter.step();
			System.out.println(interpreter.getDataModel().evalAsString("'FOO' / qwer"));
		}

		
		
	}

}
