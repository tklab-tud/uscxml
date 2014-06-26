using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace EmbeddedInvoker
{
    class TestInvoker : Invoker
    {
        public override DataNative getDataModelVariables()
        {
            DataNative data = new DataNative();
            return data;
        }

        public override StringList getNames()
        {
            StringList names = new StringList();
            names.add("simple");
            return names;
        }

        public override void invoke(InvokeRequest req)
        {
        }

        public override void send(SendRequest req)
        {
        }
    }
}
