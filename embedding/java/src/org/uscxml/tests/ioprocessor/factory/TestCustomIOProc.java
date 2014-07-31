package org.uscxml.tests.ioprocessor.factory;

import java.io.IOException;
import java.io.StringReader;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.Factory;
import org.uscxml.IOProcessor;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.SendRequest;
import org.uscxml.StringList;
import org.w3c.dom.Document;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public class TestCustomIOProc extends IOProcessor {

	public Interpreter interpreter;

	/**
	 * The types we will handle on a <send> element
	 */
	@Override
	public StringList getNames() {
		StringList ss = new StringList();
		ss.add("java");
		return ss;
	}

	/**
	 * Optional data we want to make available at
	 * _ioprocessors[this.getNames.front()] in the datamodel
	 */
	@Override
	public Data getDataModelVariables() {
		return new Data();
	}

	/**
	 * Send from the SCXML interpreter to this ioprocessor
	 */
	@Override
	public void send(SendRequest req) {
		System.out.println(req);
		// send in s1.onentry
		if ("This is some content!".equals(req.getContent())) {
			returnEvent(new Event("received1"));
			return;
		}
		// send in s2.onentry
		if (req.getParams().containsKey("foo")
				&& "bar".equals(req.getParams().get("foo").get(0).getAtom())) {
			returnEvent(new Event("received2"));
			return;
		}
		// send in s3
		if (req.getXML().length() > 0) {
			try {
				DocumentBuilderFactory factory = DocumentBuilderFactory
						.newInstance();
				Document doc = factory.newDocumentBuilder().parse(
						new InputSource(new StringReader(req.getXML())));
				System.out.println("Root element :"
						+ doc.getDocumentElement().getNodeName());
				if ("this".equals(doc.getDocumentElement().getNodeName())) {
					returnEvent(new Event("received3"));
					return;
				}
			} catch (ParserConfigurationException e) {
				e.printStackTrace();
			} catch (SAXException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

	}

	/**
	 * Create a new instance of this
	 */
	@Override
	public IOProcessor create(Interpreter interpreter) {
		TestCustomIOProc ioProc = new TestCustomIOProc();
		ioProc.interpreter = interpreter;
		ioProc.swigReleaseOwnership();
		return ioProc;
	}

	/**
	 * @param args
	 * @throws InterpreterException
	 */
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		TestCustomIOProc ioproc = new TestCustomIOProc();
		// just register prototype at global factory
		Factory.getInstance().registerIOProcessor(ioproc);
		
		String xml = 
		"<scxml>" +
		"  <state id=\"s1\">" +
		"    <onentry>" +
		"      <send type=\"java\">" +
		"        <content>This is some content!</content>" +
		"      </send>" +
		"    </onentry>" +
		"    <transition event=\"received1\" target=\"s2\" />" +
		"  </state>" +
		"  <state id=\"s2\">" +
		"    <onentry>" +
		"      <send type=\"java\">" +
		"        <param name=\"foo\" expr=\"bar\" />" +
		"      </send>" +
		"    </onentry>" +
		"    <transition event=\"received2\" target=\"s3\" />" +
		"  </state>" +
		"  <state id=\"s3\">" +
		"    <onentry>" +
		"      <send type=\"java\">" +
		"        <content>" +
		"        <this><is><xml/></is></this>" +
		"        </content>" +
		"      </send>" +
		"    </onentry>" +
		"    <transition event=\"received3\" target=\"done\" />" +
		"  </state>" +
		"  <final id=\"done\" />" +
		"</scxml>";

		// parse and interpret
		Interpreter interpreter = Interpreter.fromXML(xml);
		interpreter.interpret();
	}

}
