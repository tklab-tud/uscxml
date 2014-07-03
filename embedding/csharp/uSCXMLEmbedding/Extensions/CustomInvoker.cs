using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;
using System.Xml;
using System.Xml.XPath;
using System.IO;

namespace embedding
{
    class CustomInvoker : Invoker
    {
        public override Invoker create(Interpreter interpreter)
        {
            CustomInvoker invoker = new CustomInvoker();
            invoker.swigCMemOwn = false;
            return invoker;
        }

        public override Data getDataModelVariables()
        {
            Data data = new Data();
            return data;
        }

        public override StringList getNames()
        {
            StringList names = new StringList();
            names.add("custom");
            return names;
        }

        public override void invoke(InvokeRequest req)
        {
            Console.WriteLine(req);
            // send in s1.onentry
            if ("Some string content" == req.getContent())
            {
                returnEvent(new Event("received1"), true);
                return;
            }
        }

        public override void send(SendRequest req)
        {
            Console.WriteLine(req);
            // send in s2.onentry
            if (req.getName() == "foo")
            {
                returnEvent(new Event("received2"));
                return;
            }
            // send in s3
            if (req.getXML().Length > 0)
            {
                XmlReaderSettings set = new XmlReaderSettings();
                set.ConformanceLevel = ConformanceLevel.Fragment;
                XPathDocument doc = new XPathDocument(XmlReader.Create(new StringReader(req.getXML()), set));
                XPathNavigator nav = doc.CreateNavigator();

                Console.WriteLine("Root element :" + nav.SelectSingleNode("/").Value);
                returnEvent(new Event("received3"));
                return;
            }

        }
    }
}
