package org.uscxml.examples;

import java.net.URL;

//import org.uscxml.apache.commons.scxml2.*;
import org.apache.commons.scxml2.*;
import org.apache.commons.scxml2.env.SimpleErrorReporter;
import org.apache.commons.scxml2.env.jexl.JexlEvaluator;
import org.apache.commons.scxml2.io.SCXMLReader;
import org.apache.commons.scxml2.model.SCXML;

public class ApacheCommonsAPI {

    // SCXML model source URL
    private static final URL SCXML = ApacheCommonsAPI.class.getResource("hello-world.xml");

    public static void main(String [] args) throws Exception {
		String uSCXMLLibPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava.jnilib"; 
		if (System.getenv().containsKey("USCXML_JAVA_LIB")) {
			uSCXMLLibPath = System.getenv("USCXML_JAVA_LIB");
		}
		
		System.load(uSCXMLLibPath);

    	
    	// evaluator instance which is used by SCXML engine to evaluate expressions in SCXML
        Evaluator evaluator = new JexlEvaluator();
        // engine to execute the scxml instance
        SCXMLExecutor executor = new SCXMLExecutor(evaluator, null, new SimpleErrorReporter());

        // parse SCXML URL into SCXML model
        SCXML scxml = SCXMLReader.read(SCXML);
        // set state machine (scxml instance) to execute
        executor.setStateMachine(scxml);

        // create root context storing variables and being used by evaluator
        Context rootContext = evaluator.newContext(null);
        // set the root context for the engine
        executor.setRootContext(rootContext);

        // initiate the execution of the state machine
        executor.go();
    }

}
