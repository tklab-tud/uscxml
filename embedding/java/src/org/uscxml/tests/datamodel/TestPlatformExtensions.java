package org.uscxml.tests.datamodel;

import org.uscxml.Data;
import org.uscxml.DataModelExtension;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;
import org.uscxml.InterpreterState;

public class TestPlatformExtensions extends DataModelExtension {

	/* Currently only with ECMAScript datamodels! */
	
	@Override
	public String provides() {
		return "_x.platform.pool";
	}

	@Override
	public Data getValueOf(String member) {
		return new Data(true);
	}
	
	@Override
	public void setValueOf(String member, Data data) {
		System.out.println("Setting " + member + " to \n" + data);
	}

	public static void main(String[] args) throws InterpreterException {
		// load JNI library from build directory
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		TestPlatformExtensions ext = new TestPlatformExtensions();
		
		String xml = 
		"<scxml datamodel=\"ecmascript\">" +
		"  <script src=\"http://uscxml.tk.informatik.tu-darmstadt.de/scripts/dump.js\" />" +
		"  <state id=\"s1\">" +
		"    <onentry>" +
        "      <script>_x.platform.pool('member.second', { foo: 12, bar: 34})</script>" +
        "      <log label=\"ext\" expr=\"dump(_x.platform.pool('member.first'))\" />" +
        "    </onentry>" +
		"    <transition target=\"done\" />" +		
		"  </state>" +
		"  <final id=\"done\" />" +
		"</scxml>";

		Interpreter interpreter = Interpreter.fromXML(xml);
		interpreter.addDataModelExtension(ext);

		InterpreterState state;
		
		do {
			state = interpreter.step();			
		} while (state != InterpreterState.USCXML_FINISHED && 
				 state != InterpreterState.USCXML_DESTROYED);

	}

}
