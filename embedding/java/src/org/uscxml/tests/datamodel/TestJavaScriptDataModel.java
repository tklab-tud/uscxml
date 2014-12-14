package org.uscxml.tests.datamodel;

import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.datamodel.ecmascript.ECMAScriptDataModel;

public class TestJavaScriptDataModel {

	public static void main(String[] args) throws InterpreterException {
		// load JNI library from build directory
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		// register java datamodel at factory
		ECMAScriptDataModel datamodel = new ECMAScriptDataModel();
		Factory.getInstance().registerDataModel(datamodel);

		// instantiate interpreter with document from file
		Interpreter interpreter = Interpreter
				.fromURL("/Users/sradomski/Documents/TK/Code/uscxml/test/uscxml/java/test-ecmascript-datamodel.scxml");

		// wait until interpreter has finished
		while (true)
			interpreter.interpret();
	}

}
