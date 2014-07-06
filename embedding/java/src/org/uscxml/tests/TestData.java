package org.uscxml.tests;

import org.uscxml.Blob;
import org.uscxml.Data;

public class TestData {

	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");
		{
			Data data = Data.fromJSON("[1,2,3,4,5]");
			System.out.println(data);
		}
		{
			Data data = Data.fromJSON("{ \"foo\": \"bar\", \"faz\": 12 }");
			System.out.println(data);
		}
		
		{
			byte binData[] = new byte[1024];
			Data data = new Data(binData, "application/octet-stream");
		}
		
	}
}
