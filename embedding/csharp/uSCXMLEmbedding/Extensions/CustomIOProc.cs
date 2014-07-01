using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class CustomIOProc : IOProcessor
    {
        public override IOProcessor create(Interpreter interpreter)
        {
            return new CustomIOProc();
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

        public override void send(SendRequest req)
        {
        }
    }
}
