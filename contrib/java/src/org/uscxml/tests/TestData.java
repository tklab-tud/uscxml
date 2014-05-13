package org.uscxml.tests;

import org.uscxml.Data;
import org.uscxml.DataNative;

public class TestData {

	public static void main(String[] args) {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64_d.jnilib");
		{
			Data data = Data.fromJSON("[1,2,3,4,5]");
			DataNative nData2 = Data.toNative(data);
			Data data2 = new Data(nData2);
			System.out.println(data2);
		}
		{
			Data data = Data.fromJSON("{ \"foo\": \"bar\", \"faz\": 12 }");
			DataNative nData2 = Data.toNative(data);
			Data data2 = new Data(nData2);
			System.out.println(data2);
		}
	}
}
