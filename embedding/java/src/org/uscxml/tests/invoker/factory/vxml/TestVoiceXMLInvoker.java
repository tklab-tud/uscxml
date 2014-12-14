package org.uscxml.tests.invoker.factory.vxml;

import java.io.IOException;
import java.net.URL;

import org.uscxml.HTTPServer;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;

public class TestVoiceXMLInvoker {

	public static void main(String[] args) throws IOException, InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		HTTPServer http = HTTPServer.getInstance(5080, 5081);
		
		URL jVoiceXMLDoc = new URL(new URL("file:"), "../../test/uscxml/test-jvoicexml.scxml");
		Interpreter interpreter = Interpreter.fromURL(jVoiceXMLDoc);
		interpreter.interpret();
	}

}
