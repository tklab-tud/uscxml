using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Runtime.InteropServices;

namespace embedding
{
    using org.uscxml;

    class Program
    {
        [DllImport("kernel32.dll", CharSet = CharSet.Auto)]
        private static extern void SetDllDirectory(string lpPathName);

        static bool testLifecycle() {
            // try to instantiate an interpreter with a parse error
            try
            {
                Interpreter interpreter = Interpreter.fromXML("<invalid");
                Debug.Assert(false);
            }
            catch (InterpreterException e) {
                Console.Write(e.Message);
            }

            // try to instantiate an interpreter with invalid XML (no scxml element)
            try
            {
                Interpreter interpreter = Interpreter.fromXML("<invalid />");
                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                InterpreterState state = interpreter.step();

                Debug.Assert(false);
            }
            catch (InterpreterException e)
            {
                Console.Write(e.Message);
            }

            return true;
        }

        static void Main(string[] args)
        {

            /*
             * Make sure this path contains the uscxmlNativeCSharp.dll!
             */
            if (System.Environment.Is64BitProcess)
            {
                SetDllDirectory("C:\\Users\\sradomski\\Desktop\\build\\uscxml64\\lib\\csharp");
            }
            else
            {
                SetDllDirectory("C:\\Users\\sradomski\\Desktop\\build\\uscxml\\lib\\csharp");
            }

            testLifecycle();
            Console.ReadKey();
        }
    }
}
