package org.uscxml.tests;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InvokeRequest;
import org.uscxml.JavaInvoker;
import org.uscxml.SendRequest;
import org.uscxml.StringSet;


public class TestInvoker extends JavaInvoker {

	@Override
	public StringSet getNames() {
		StringSet ss = new StringSet();
		ss.insert("java");
		return ss;
	}

	@Override
	public Data getDataModelVariables() {
		Data data = new Data();
		data.getArray().add(new Data("foo", Data.Type.VERBATIM));
		return data;
	}

	@Override
	public void send(SendRequest req) {
		System.out.println("send");
	}

	@Override
	public void invoke(InvokeRequest req) {
		System.out.println("invoke");

		System.out.println(Data.toJSON(req.getData()));
		System.out.println(req.getXML());
		
		Event ev = new Event();
		ev.setName("foo");
		returnEvent(ev);
	}

	@Override
	public JavaInvoker create(Interpreter interpreter) {
		return new TestInvoker();
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64_d.jnilib");
		
		TestInvoker invoker = new TestInvoker(); 
		Factory.getInstance().registerInvoker(invoker);
		
		Interpreter interpreter = Interpreter.fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/test-java-invoker.scxml");
		while(true)
			interpreter.interpret();
	}

}
