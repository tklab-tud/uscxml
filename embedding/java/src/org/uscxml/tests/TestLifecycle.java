package org.uscxml.tests;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;

public class TestLifecycle {
	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		// syntactic xml parse error -> throws
		try {
			String xml = "<invalid";
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			throw new RuntimeException("");
		} catch (InterpreterException e) {
			System.err.println(e);
		}

		// semantic xml parse error -> throws
		try {
			String xml = "<invalid />";
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			if (interpreter.getState() != InterpreterState.USCXML_INSTANTIATED) throw new RuntimeException("");
			interpreter.step();
			throw new RuntimeException("");
		} catch (InterpreterException e) {
			System.err.println(e);
		}

		// request unknown datamodel -> throws
		try {
			String xml =
			"<scxml datamodel=\"invalid\">" +
			"	<state id=\"start\">" +
			"		<transition target=\"done\" />" +
			" </state>" +
			" <final id=\"done\" />" +
			"</scxml>"; 
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			if (interpreter.getState() != InterpreterState.USCXML_INSTANTIATED)  throw new RuntimeException("");
			interpreter.step();
			throw new RuntimeException("");
			
		} catch (InterpreterException e) {
			System.err.println(e);
		}

		try {
			// two microsteps
			String xml =
			"<scxml>" +
			"	<state id=\"start\">" +
			"		<transition target=\"s2\" />" +
			"   </state>" +
			"	<state id=\"s2\">" +
			"		<transition target=\"done\" />" +
			" </state>" +
			" <final id=\"done\" />" +
			"</scxml>";
			
			Interpreter interpreter = Interpreter.fromXML(xml, "");

			if (interpreter.getState() != InterpreterState.USCXML_INSTANTIATED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_MICROSTEPPED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_MICROSTEPPED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_FINISHED) throw new RuntimeException("");

		} catch (InterpreterException e) {
			System.err.println(e);
		}
	
		try {
			// single macrostep, multiple runs
			String xml =
			"<scxml>" +
			"	<state id=\"start\">" +
			"		<transition target=\"done\" />" +
			" </state>" +
			" <final id=\"done\" />" +
			"</scxml>";
			
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			if (interpreter.getState() != InterpreterState.USCXML_INSTANTIATED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_MICROSTEPPED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_FINISHED) throw new RuntimeException("");
			interpreter.reset();

			if (interpreter.getState() != InterpreterState.USCXML_INSTANTIATED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_MICROSTEPPED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_FINISHED) throw new RuntimeException("");

		} catch (InterpreterException e) {
			System.err.println(e);
		}
		
		try {
			// macrostep in between
			String xml =
			"<scxml>" +
			"	<state id=\"start\">" +
			"		<onentry>" +
			"			<send event=\"continue\" delay=\"2s\"/>" +
			"		</onentry>" +
			"		<transition target=\"s2\" event=\"continue\" />" +
			" </state>" +
			"	<state id=\"s2\">" +
			"		<transition target=\"done\" />" +
			" </state>" +
			" <final id=\"done\" />" +
			"</scxml>";
			
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			if (interpreter.getState() != InterpreterState.USCXML_INSTANTIATED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_IDLE) throw new RuntimeException("");
			if (interpreter.step(true) != InterpreterState.USCXML_MACROSTEPPED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_MICROSTEPPED) throw new RuntimeException("");
			if (interpreter.step() != InterpreterState.USCXML_FINISHED) throw new RuntimeException("");

		} catch (InterpreterException e) {
			System.err.println(e);
		}
	}
}
