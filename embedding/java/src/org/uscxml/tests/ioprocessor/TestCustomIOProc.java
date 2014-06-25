package org.uscxml.tests.ioprocessor;

import org.uscxml.Data;
import org.uscxml.DataNative;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.SendRequest;
import org.uscxml.StringList;
import org.uscxml.WrappedIOProcessor;

public class TestCustomIOProc extends WrappedIOProcessor {

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
	public WrappedIOProcessor create(Interpreter interpreter) {
		return new TestCustomIOProc();
	}

	/**
	 * @param args
	 * @throws InterpreterException 
	 */
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64_d.jnilib");

		TestCustomIOProc ioproc = new TestCustomIOProc();
		Factory.getInstance().registerIOProcessor(ioproc);

		Interpreter interpreter = Interpreter
				.fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/test-java-invoker.scxml");
		while (true)
			interpreter.interpret();
	}

}
