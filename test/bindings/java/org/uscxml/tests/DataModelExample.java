package org.uscxml.tests;

import java.io.File;
import java.net.MalformedURLException;

import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;
import org.uscxml.dm.jexl.JEXLDataModel;
import org.uscxml.tests.helper.TestMonitor;

public class DataModelExample {

	public static void main(String[] args) {
		String uSCXMLLibPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava.jnilib"; 
		if (System.getenv().containsKey("USCXML_JAVA_LIB")) {
			uSCXMLLibPath = System.getenv("USCXML_JAVA_LIB");
		}
		
		System.load(uSCXMLLibPath);
		
		JEXLDataModel jdm = new JEXLDataModel();
		Factory.getInstance().registerDataModel(jdm);;
		
		TestMonitor tm = new TestMonitor();

		File folder = new File("/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/jexl");
		File[] listOfFiles = folder.listFiles();
		
		try {
			for (File file : listOfFiles) {
				if (!file.getName().endsWith(".scxml"))
					continue;
				String testName = file.toURI().toURL().toString();
				System.out.println(testName);
				
				Interpreter scxml = Interpreter.fromURL(testName);
//				scxml.setMonitor(tm);
				
				while(scxml.step() != InterpreterState.USCXML_FINISHED) {}
				
				if (!scxml.isInState("pass")) {
					System.out.println("FAIL: " + testName);

					throw new RuntimeException();
				}
				System.out.println("SUCCESS");

			}
			
		} catch (InterpreterException | MalformedURLException e) {
			e.printStackTrace();
		}

	}

}
