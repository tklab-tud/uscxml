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
             * Make sure this path contains the umundoNativeCSharp.dll!
             */
            if (System.Environment.Is64BitProcess)
            {
                SetDllDirectory("C:\\Users\\sradomski\\Desktop\\build\\lib\\csharp64");
            }
            else
            {
                SetDllDirectory("C:\\Users\\sradomski\\Desktop\\build\\lib\\csharp");
            }

            Interpreter interpreter = Interpreter.fromXML("<scxml><state id=\"foo\"/></scxml>");
            interpreter.interpret();
        }
    }
}
