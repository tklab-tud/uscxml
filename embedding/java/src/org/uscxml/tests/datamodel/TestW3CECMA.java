package org.uscxml.tests.datamodel;

import java.io.File;

import org.uscxml.Capabilities;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterOptions;
import org.uscxml.datamodel.ecmascript.ECMAScriptDataModel;

public class TestW3CECMA {

	public static String testDir = "/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma";
	
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		ECMAScriptDataModel datamodel = new ECMAScriptDataModel();
		Factory.getInstance().registerDataModel(datamodel);

//		while(true) {
//	    	System.out.println("### test235 #####");
//			Interpreter interpreter = Interpreter.fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma/test144.scxml");
//			interpreter.interpret();
//		}
		
		File dir = new File(testDir);
		File[] filesList = dir.listFiles();
		for (File file : filesList) {
		    if (file.isFile() && file.getName().endsWith(".scxml")) {
		    	System.out.println("### " + file.getName() + " #####");
		    	Interpreter interpreter = Interpreter.fromURI(file.getAbsolutePath());
		    	interpreter.setCapabilities(1);
		    	interpreter.interpret();
		    }
		}

	}

}
