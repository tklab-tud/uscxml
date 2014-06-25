package org.uscxml.tests.invoker;

import org.uscxml.Data;
import org.uscxml.DataNative;
import org.uscxml.Event;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InvokeRequest;
import org.uscxml.StringList;
import org.uscxml.WrappedInvoker;
import org.uscxml.SendRequest;
import org.uscxml.StringSet;

public class TestCustomInvoker extends WrappedInvoker {

	@Override
	public StringList getNames() {
		StringList ss = new StringList();
		ss.add("java");
		return ss;
	}

	@Override
	public DataNative getDataModelVariables() {
		Data data = new Data();
		data.array.add(new Data("foo", Data.Type.VERBATIM));
		return Data.toNative(data);
	}

	@Override
	public void send(SendRequest req) {
		System.out.println("send");
	}

	@Override
	public void invoke(InvokeRequest req) {
		System.out.println("invoke");

		System.out.println(req.getData());
		System.out.println(req.getXML());

		Event ev = new Event();
		ev.setName("foo");
		returnEvent(ev);
	}

	@Override
	public WrappedInvoker create(Interpreter interpreter) {
		return new TestCustomInvoker();
	}

	/**
	 * @param args
	 * @throws InterpreterException 
	 */
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64_d.jnilib");

		TestCustomInvoker invoker = new TestCustomInvoker();
		Factory.getInstance().registerInvoker(invoker);

		Interpreter interpreter = Interpreter
				.fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/test-java-invoker.scxml");
		while (true)
			interpreter.interpret();
	}

}
