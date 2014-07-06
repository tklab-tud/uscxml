package org.uscxml.tests;

import org.uscxml.Blob;
import org.uscxml.BlobImpl;
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
			byte origData[] = new byte[1024];
			for (int i = 0; i < origData.length; i++) {
				origData[i] = (byte)i;
			}
			
			{
				Blob blob = new Blob(origData, "application/octet-stream");
				if (origData.length != blob.getSize()) throw new RuntimeException("Blob does not match");

				for (int i = 0; i < origData.length; i++) {
					if (origData[i] != blob.getData()[i])
						throw new RuntimeException("Blob mismatch at " + i);
				}
			}
			
			Data data = new Data(origData, "application/octet-stream");
			Blob blob = data.getBinary();
			System.out.println(blob.getSize());
			
			byte newData[] = blob.getData();
			
			if (newData.length != origData.length) throw new RuntimeException("Arrays length does not match");
			for (int i = 0; i < origData.length; i++) {
				if (newData[i] != origData[i])
					throw new RuntimeException("Mismatch at " + i);
			}
			
		}
		
	}
}
