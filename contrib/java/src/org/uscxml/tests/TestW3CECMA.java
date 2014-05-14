package org.uscxml.tests;

import java.io.File;

import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.datamodel.ecmascript.ECMAScriptDataModel;

public class TestW3CECMA {

	public static String testDir = "/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma";
	
	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		ECMAScriptDataModel datamodel = new ECMAScriptDataModel();
		Factory.getInstance().registerDataModel(datamodel);

//    	Interpreter interpreter = Interpreter.fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/ecma/test176.scxml");
//    	interpreter.interpret();
//    	System.exit(0);
		
		File dir = new File(testDir);
		File[] filesList = dir.listFiles();
		for (File file : filesList) {
		    if (file.isFile() && file.getName().endsWith(".scxml")) {
		    	System.out.println("### " + file.getName() + " #####");
		    	Interpreter interpreter = Interpreter.fromURI(file.getAbsolutePath());
		    	interpreter.interpret();
		    }
		}

	}

}
