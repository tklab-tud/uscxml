package org.uscxml.tests;

import java.io.File;
import java.net.MalformedURLException;

import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;
import org.uscxml.dm.jexl.JEXLDataModel;
import org.uscxml.helper.TestMonitor;

public class JexlDataModelTest {

	public static void main(String[] args) {
		String uSCXMLLibPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava.jnilib";
		if (System.getenv().containsKey("USCXML_JAVA_LIB")) {
			uSCXMLLibPath = System.getenv("USCXML_JAVA_LIB");
		}

		System.load(uSCXMLLibPath);
		String testUri = "/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/jexl/test144.scxml";

		if (args.length > 0) {
			testUri = args[0];
		}

		{
			JEXLDataModel jdm = new JEXLDataModel();
			Factory.getInstance().registerDataModel(jdm);

			TestMonitor tm = new TestMonitor();

			try {
				File testFile = new File(testUri);
				String testName = testFile.toURI().toURL().toString();
				System.out.println(testName);

				Interpreter scxml = Interpreter.fromURL(testName);
				scxml.setMonitor(tm);

				while (scxml.step() != InterpreterState.USCXML_FINISHED) {
				}

				if (!scxml.isInState("pass")) {
					System.out.println("FAIL: " + testName);
					throw new RuntimeException();
				}
				System.out.println("SUCCESS");

			} catch (InterpreterException | MalformedURLException e) {
				e.printStackTrace();
				System.exit(-1);
			}
		}

		 System.exit(0);
	}

}
