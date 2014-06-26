using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class TestExecutableContent : ExecutableContent
    {
        public override string getLocalName()
        {
            return "custom";
        }

        public override void enterElement(string node)
        {
            
        }

        public override void exitElement(string node)
        {
            
        }

        public override ExecutableContent create(Interpreter interpreter) 
        {
            return new TestExecutableContent();
        }


    }
}
