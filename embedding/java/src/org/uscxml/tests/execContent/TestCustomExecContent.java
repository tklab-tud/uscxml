package org.uscxml.tests.execContent;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.ExecutableContent;

public class TestCustomExecContent extends ExecutableContent {

	static int instanceId = 0;
	public int id = 0;
	
	public TestCustomExecContent() {
		id = instanceId++;
	} 

	@Override
	public String getLocalName() {
		return "custom";
	}

	@Override
	public String getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}


	@Override
	public void enterElement(String node) {
		System.out.println(id + " entering:" + node);
	}

	@Override
	public void exitElement(String node) {
		System.out.println(id + " exiting:" + node);
	}

	@Override
	public boolean processChildren() {
		return false;
	}

	@Override
	public ExecutableContent create(Interpreter interpreter) {
		return new TestCustomExecContent();
	}

	/**
	 * @param args
	 * @throws InterruptedException 
	 * @throws InterpreterException 
	 */
	public static void main(String[] args) throws InterruptedException, InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		TestCustomExecContent execContent = new TestCustomExecContent();
		Factory.getInstance().registerExecutableContent(execContent);

		Interpreter interpreter = Interpreter.fromXML(
						"<scxml>\n" +
						"  <state id=\"s0\">\n" +
						"    <onentry>\n" +
						"      <custom foo=\"bar\">\n" +
						"        <something></something>\n" +
						"      </custom>\n" +
						"      <custom foo=\"bar\">\n" +
						"        <something></something>\n" +
						"      </custom>\n" +
						"    </onentry>\n" +
						"    <transition target=\"exit\" />" +
						"  </state>\n" +
						"  <final id=\"exit\" />" +
						"</scxml>\n"
				);
		interpreter.interpret();
		Thread.sleep(1000);
	}

}
