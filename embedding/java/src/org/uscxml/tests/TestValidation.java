package org.uscxml.tests;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.IssueList;

public class TestValidation {

	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		// invalid expression in transition
		try {
			String xml =
			"<scxml datamodel=\"ecmascript\">" +
			"	<state id=\"start\">" +
			"		<transition target=\"don\" cond=\"%sf\" />" +
			" </state>" +
			" <final />" +
			"</scxml>"; 
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			IssueList issues = interpreter.validate();
			for (int i = 0; i < issues.size(); i++) {
				System.out.println(issues.get(i));
			}
						
		} catch (InterpreterException e) {
			System.err.println(e);
		}

	}

}
