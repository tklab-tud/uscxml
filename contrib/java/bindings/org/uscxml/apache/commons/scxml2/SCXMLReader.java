package org.uscxml.apache.commons.scxml2;

import java.net.URL;

public class SCXMLReader {

	public static SCXML read(URL scxml) {
		SCXML foo = new SCXML();
		foo.url = scxml;
		return foo;
	}

}
