package org.uscxml.tests;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.JavaDataModel;
import org.uscxml.SWIGTYPE_p_Arabica__DOM__DocumentT_std__string_t;
import org.uscxml.SWIGTYPE_p_Arabica__DOM__ElementT_std__string_t;
import org.uscxml.SWIGTYPE_p_boost__shared_ptrT_uscxml__DataModelImpl_t;
import org.uscxml.SWIGTYPE_p_uscxml__InterpreterImpl;
import org.uscxml.StringSet;


public class TestDataModel extends JavaDataModel {
	
	@Override
	public JavaDataModel create(Interpreter interpreter) {
		return new JavaDataModel();
	}

	@Override
	public StringSet getNames() {
		StringSet ss = new StringSet();
		ss.insert("java");
		return ss;
	}

	@Override
	public boolean validate(String location, String schema) {
		return true;
	}

	@Override
	public void setEvent(Event event) {
		/* make sure the fields of event are available as _event to conform
		 * with the SCXML draft
		 */
	}

	@Override
	public Data getStringAsData(String content) {
		Data data = new Data();
		return data;
	}

	@Override
	public long getLength(String expr) {
		return 0;
	}

	@Override
	public void setForeach(String item, String array, String index, long iteration) {
	}

	@Override
	public void eval(SWIGTYPE_p_Arabica__DOM__ElementT_std__string_t scriptElem, String expr) {
	}

	@Override
	public String evalAsString(String expr) {
		return "";
	}

	@Override
	public boolean evalAsBool(String expr) {
		return true;
	}

	@Override
	public boolean isDeclared(String expr) {
		return true;
	}

	@Override
	public void assign(SWIGTYPE_p_Arabica__DOM__ElementT_std__string_t assignElem, SWIGTYPE_p_Arabica__DOM__DocumentT_std__string_t doc, String content) {
	}

	@Override
	public void assign(String location, Data data) {
		super.assign(location, data);
	}

	@Override
	public void init(SWIGTYPE_p_Arabica__DOM__ElementT_std__string_t dataElem, SWIGTYPE_p_Arabica__DOM__DocumentT_std__string_t doc, String content) {
		super.init(dataElem, doc, content);
	}

	@Override
	public void init(String location, Data data) {
		super.init(location, data);
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64_d.jnilib");
		
		TestDataModel datamodel = new TestDataModel(); 
		Factory.getInstance().registerDataModel(datamodel);
		
		Interpreter interpreter = Interpreter.fromURI("/Users/sradomski/Documents/TK/Code/uscxml/test/samples/uscxml/test-java-datamodel.scxml");
		while(true)
			interpreter.interpret();
	}

}
