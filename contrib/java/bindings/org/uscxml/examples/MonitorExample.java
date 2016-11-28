package org.uscxml.examples;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;
import org.uscxml.StringVector;
import org.uscxml.helper.TestMonitor;


public class MonitorExample {
	
	public static void main(String[] args) {
		
		String uSCXMLLibPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava.jnilib"; 
		if (System.getenv().containsKey("USCXML_JAVA_LIB")) {
			uSCXMLLibPath = System.getenv("USCXML_JAVA_LIB");
		}
		
		System.load(uSCXMLLibPath);
		
		try {
			TestMonitor tm = new TestMonitor();
			Interpreter scxml = Interpreter.fromURL("https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml");
			scxml.addMonitor(tm);
			InterpreterState state = InterpreterState.USCXML_UNDEF;
			while((state = scxml.step()) != InterpreterState.USCXML_FINISHED) {
				switch (state) {
				case USCXML_FINISHED:
				case USCXML_UNDEF:
				case USCXML_IDLE:
				case USCXML_INITIALIZED:
				case USCXML_INSTANTIATED:
					break;
				case USCXML_MICROSTEPPED:
				case USCXML_MACROSTEPPED:
					StringVector states = scxml.getConfiguration();
					for (int i = 0; i < states.size(); i++) {
						System.out.print(states.get(i) + " ");
					}
					System.out.println();
				case USCXML_CANCELLED:
					break;
				default:
					break;
				}
			}
			
		} catch (InterpreterException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		System.exit(0);
	}

}
