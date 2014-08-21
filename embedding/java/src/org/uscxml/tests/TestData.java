package org.uscxml.tests;

import java.io.StringWriter;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.uscxml.Blob;
import org.uscxml.Data;
import org.w3c.dom.Document;

public class TestData {

	public static void main(String[] args) throws Exception {
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
			Data data = new Data();

			DocumentBuilderFactory factory = DocumentBuilderFactory
					.newInstance();
			DocumentBuilder builder = factory.newDocumentBuilder();

			Document document = builder.newDocument();
			document.appendChild(document.createElement("foo"));

			Transformer transformer = TransformerFactory.newInstance()
					.newTransformer();
			StreamResult result = new StreamResult(new StringWriter());
			DOMSource source = new DOMSource(document);
			transformer.transform(source, result);

			String xml = result.getWriter().toString();

			data.setXML(xml);
			System.out.println(data.getXML());
		}

		{
			byte origData[] = new byte[1024];
			for (int i = 0; i < origData.length; i++) {
				origData[i] = (byte) i;
			}

			{
				Blob blob = new Blob(origData, "application/octet-stream");
				if (origData.length != blob.getSize())
					throw new RuntimeException("Blob does not match");

				for (int i = 0; i < origData.length; i++) {
					if (origData[i] != blob.getData()[i])
						throw new RuntimeException("Blob mismatch at " + i);
				}
			}

			Data data = new Data(origData, "application/octet-stream");
			Blob blob = data.getBinary();
			System.out.println(blob.getSize());

			byte newData[] = blob.getData();

			if (newData.length != origData.length)
				throw new RuntimeException("Arrays length does not match");
			for (int i = 0; i < origData.length; i++) {
				if (newData[i] != origData[i])
					throw new RuntimeException("Mismatch at " + i);
			}

		}

	}
}
