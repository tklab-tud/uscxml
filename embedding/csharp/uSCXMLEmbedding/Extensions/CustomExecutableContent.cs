using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class CustomExecutableContent : ExecutableContent
    {
        public override string getLocalName()
        {
            return "custom";
        }

        public override void enterElement(string node)
        {
            Console.WriteLine("enterElement " + node);
        }

        public override void exitElement(string node)
        {
            Console.WriteLine("exitElement " + node);
        }

        public override ExecutableContent create(Interpreter interpreter) 
        {
            CustomExecutableContent execContent = new CustomExecutableContent();
            execContent.swigCMemOwn = false;
            return execContent;
        }


    }
}
