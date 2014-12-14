package org.uscxml.tests.datamodel;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;

public class TestDataModelAccess {
	public static void main(String[] args) throws InterpreterException {
		// load JNI library from build directory
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		{
			// initializing and accessing complex data
			String xml = 
			"<scxml datamodel=\"ecmascript\">" +
			"  <script src=\"http://uscxml.tk.informatik.tu-darmstadt.de/scripts/dump.js\" />" +
			"  <datamodel>" +
			"    <data id=\"cmplx1\"><![CDATA[" +
			"      { foo: \"bar\", baz: 12 }" +
			"	 ]]></data>" +
			"    <data id=\"cmplx2\">" +
			"      <inline><xml foo=\"sdfasdf\"/></inline>" +
			"    </data>" +
			"  </datamodel>" +
			"  <state id=\"s1\">" +
			"    <onentry>" +
	        "      <log label=\"cmplx1\" expr=\"cmplx1.foo\" />" +
	        "      <log label=\"cmplx1\" expr=\"cmplx1.baz\" />" +
	        "      <script>dump(cmplx1)</script>" +
	        "" +
	        "      <log label=\"cmplx2\" expr=\"document.evaluate('//xml/@foo').asString()\" />" +
	        "    </onentry>" +
			"    <transition target=\"done\" />" +		
			"  </state>" +
			"  <final id=\"done\" />" +
			"</scxml>";
				
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			InterpreterState state;
			do {
				state = interpreter.step();
				// after first microstep, data model is initialized and we can access cmplx1
				if (state == InterpreterState.USCXML_MICROSTEPPED)
					System.out.println(interpreter.getDataModel().getStringAsData("cmplx1").toString());
				
			} while (state != InterpreterState.USCXML_FINISHED && 
					 state != InterpreterState.USCXML_DESTROYED);
		}
		
		{
			// initializing and accessing complex data via data.src
			String xml = 
			"<scxml datamodel=\"ecmascript\">" +
			"  <script src=\"http://uscxml.tk.informatik.tu-darmstadt.de/scripts/dump.js\" />" +
			"  <datamodel>" +
			"    <data id=\"cmplx1\" src=\"TestData.json\" />" +
			"    <data id=\"cmplx2\" src=\"TestData.xml\" />" +
			"  </datamodel>" +
			"  <state id=\"s1\">" +
			"    <onentry>" +
			"      <script>" +
			"        var node = document.evaluate('//to', cmplx2);" +
			"        dump(node.asString());" +
			"      </script>" +
			"      <log label=\"cmplx1\" expr=\"cmplx1.name\" />" +
	        "      <log label=\"cmplx1\" expr=\"cmplx1.price\" />" +
	        "      <script>dump(cmplx1)</script>" +
			"    </onentry>" +
			"    <transition target=\"done\" />" +		
			"  </state>" +
			"  <final id=\"done\" />" +
			"</scxml>";
				
			Interpreter interpreter = Interpreter.fromXML(xml, "");
			interpreter.setSourceURL(TestDataModelAccess.class.getResource("").toString());
			InterpreterState state;
			do {
				state = interpreter.step();
				// after first microstep, data model is initialized and we can access cmplx1
				if (state == InterpreterState.USCXML_MICROSTEPPED)
					System.out.println(interpreter.getDataModel().getStringAsData("cmplx1").toString());
				
			} while (state != InterpreterState.USCXML_FINISHED && 
					 state != InterpreterState.USCXML_DESTROYED);

		}
	}

}
