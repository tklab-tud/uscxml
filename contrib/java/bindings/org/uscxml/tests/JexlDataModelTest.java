package org.uscxml.tests;

import java.io.File;
import java.net.MalformedURLException;

import org.uscxml.ActionLanguage;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;
import org.uscxml.dm.jexl.JexlDataModel;
import org.uscxml.helper.StopWatch;
import org.uscxml.helper.TestMonitor;

public class JexlDataModelTest {

	public static void main(String[] args) throws MalformedURLException {
		String uSCXMLLibPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava.jnilib";
		if (System.getenv().containsKey("USCXML_JAVA_LIB")) {
			uSCXMLLibPath = System.getenv("USCXML_JAVA_LIB");
		}

		System.load(uSCXMLLibPath);
		String testUri = "/Users/sradomski/Documents/TK/Code/uscxml/test/w3c/jexl/test144.scxml";
//		String testUri = "/Users/sradomski/Desktop/stopwatch.xml";

		
//		if (args.length > 0) {
//			testUri = args[0];
//		}

		{
			JexlDataModel jdm = new JexlDataModel();
			//Factory.getInstance().registerDataModel(jdm);

			
			TestMonitor tm = new TestMonitor();

			try {
				File testFile = new File(testUri);
				String testName = testFile.toURI().toURL().toString();
//				String testName = "https://raw.githubusercontent.com/woonsan/commons-scxml-examples/master/stopwatch/src/main/resources/com/github/woonsan/commons/scxml/examples/stopwatch/stopwatch.xml";
				System.out.println(testName);

				Interpreter scxml = Interpreter.fromURL(testName);
				
				//jdm.ctx.set("stopWatch", new StopWatch());
				
				ActionLanguage al = new ActionLanguage();
				al.setDataModel(jdm);
				scxml.setActionLanguage(al);
				
				scxml.addMonitor(tm);
				
				while (scxml.step() != InterpreterState.USCXML_FINISHED) {
				}

				if (!scxml.isInState("pass")) {
					System.out.println("FAIL: " + testName);
					throw new RuntimeException();
				}
				System.out.println("SUCCESS");

			} catch (InterpreterException e) {
				e.printStackTrace();
				System.exit(-1);
			}
		}

		 System.exit(0);
	}

}
