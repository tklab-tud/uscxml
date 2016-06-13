package org.uscxml.examples;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;

public class BasicExample {

	public static void main(String[] args) {
		
		String uSCXMLLibPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava.jnilib"; 
		if (System.getenv().containsKey("USCXML_JAVA_LIB")) {
			uSCXMLLibPath = System.getenv("USCXML_JAVA_LIB");
		}
		
		System.load(uSCXMLLibPath);
		
		try {
			Interpreter scxml = Interpreter.fromURL("https://raw.githubusercontent.com/tklab-tud/uscxml/master/test/w3c/null/test436.scxml");
			InterpreterState state = InterpreterState.USCXML_UNDEF;
			while((state = scxml.step()) != InterpreterState.USCXML_FINISHED) {
				switch (state) {
				case USCXML_FINISHED:
				case USCXML_UNDEF:
				case USCXML_IDLE:
				case USCXML_INITIALIZED:
				case USCXML_INSTANTIATED:
				case USCXML_MICROSTEPPED:
				case USCXML_MACROSTEPPED:
				case USCXML_CANCELLED:
					break;
				default:
					break;
				}
			}
			System.out.println("Machine finished");
			
		} catch (InterpreterException e) {
			e.printStackTrace();
			System.exit(-1);
		}
		System.exit(0);

	}

}
