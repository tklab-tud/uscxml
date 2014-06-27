using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class SampleIOProc : IOProcessor
    {
        public override IOProcessor create(Interpreter interpreter)
        {
            return new SampleIOProc();
        }

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

        public override void send(SendRequest req)
        {
        }
    }
}
