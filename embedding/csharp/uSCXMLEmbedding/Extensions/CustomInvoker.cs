using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class CustomInvoker : Invoker
    {
        public override Invoker create(Interpreter interpreter)
        {
            return new CustomInvoker();
        }

        public override Data getDataModelVariables()
        {
            Data data = new Data();
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
