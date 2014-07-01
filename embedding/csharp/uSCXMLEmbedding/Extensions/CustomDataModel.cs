using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using org.uscxml;

namespace embedding
{
    class CustomDataModel : DataModel
    {
        public override DataModel create(Interpreter interpreter)
        {
            return new CustomDataModel();
        }

        public override void eval(string scriptElem, string expr)
        {
            // evaluate expr on the datamodel
        }

        public override bool evalAsBool(string elem, string content)
        {
            return evalAsBool(content);
        }

        public override bool evalAsBool(string expr)
        {
            // evaluate expr as bool
            return false;
        }

        public override void assign(string assignElem, string location, string content)
        {
            // set variable at location to content
        }

        public override string evalAsString(string expr)
        {
            // evaluate given expr as a string (e.g. for <log>)
            return "";
        }

        public override uint getLength(string expr)
        {
            // return the length of an expression for foreach
            return 0;
        }

        public override StringList getNames()
        {
            // name of this datamodel to be used in scxml element
            StringList names  = new StringList();
            names.add("simple");
            return names;
        }

        public override Data getStringAsData(string content)
        {
            Data data = new Data();
            return data;
        }

        public override void init(string dataElem, string location, string content)
        {
            // initialize variable at location to evaluated content - used for scxml data elements
        }

        public override void setEvent(Event arg0)
        {
            // represent given event as _event in datamodel
        }

        public override bool isDeclared(string expr)
        {
            // using an undeclared variable is an error.execution with some scxml constructs - 
            // determine whether the given expression is defined
            return true;
        }

        public override void setForeach(string item, string array, string index, uint iteration)
        {
            // called per foreach iteration, set datamodel variables accordingly
        }

        public override bool validate(string location, string schema)
        {
            // primarily intended for xpath datamodel
            return true;
        }
    }
}
