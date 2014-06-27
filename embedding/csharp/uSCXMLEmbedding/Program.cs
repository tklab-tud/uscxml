using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Runtime.InteropServices;

namespace embedding
{
    using org.uscxml;

    class Program
    {
        [DllImport("kernel32.dll", CharSet = CharSet.Auto)]
        private static extern void SetDllDirectory(string lpPathName);

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

            Interpreter interpreter = Interpreter.fromXML("<scxml><state id=\"f oo\" final=\"true\" /></scxml>");
            interpreter.addMonitor(new SampleInterpreterMonitor());
            interpreter.interpret();
        }
    }
}
