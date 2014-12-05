using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics;
using System.Runtime.InteropServices;

namespace embedding
{
    using org.uscxml;

    class RunTests
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

            int i = 1;
            while (i-- > 0)
            {
                testData();
                testLifeCycle();
                testExecutableContent();
                testIOProcessor();
                testInvoker();
            }
            Console.ReadKey();
        }

        public static void testData() { 
            byte[] origData = new byte[1024];
			for (int i = 0; i < origData.Length; i++) {
				origData[i] = (byte)i;
			}
			
			{
				
                Blob blob = new Blob(origData, "application/octet-stream");
				Debug.Assert(origData.Length == blob.getSize());

				for (int i = 0; i < origData.Length; i++) {
					Debug.Assert(origData[i] == blob.getData()[i]);
				}
			}
			
			Data data = new Data(origData, "application/octet-stream");
			Blob blob2 = data.getBinary();
			
			byte[] newData = blob2.getData();
			
			if (newData.Length == origData.Length);
			for (int i = 0; i < origData.Length; i++) {
                Debug.Assert(newData[i] == origData[i]);
			}

        }

        public static void testInvoker() {
            Console.WriteLine("testInvoker");
            CustomInvoker invoker = new CustomInvoker();
            // just register prototype at global factory
            Factory.getInstance().registerInvoker(invoker);

            String xml =
            "<scxml>" +
            "  <state id=\"s1\">" +
            "    <invoke type=\"custom\" id=\"custominvoker1\">" +
            "    	<content>Some string content</content>" +
            "    </invoke>" +
            "    <invoke type=\"custom\" id=\"custominvoker2\" />" +
            "    <state id=\"s11\">" +
            "    	<transition event=\"received1\" target=\"s12\">" +
            "       </transition>" +
            "    </state>" +
            "    <state id=\"s12\">" +
            "		<onentry>" +
            "			<send target=\"#_custominvoker2\" event=\"foo\" />" +
            "           <log label=\"label\" expr=\"foo\" />" +
            "		</onentry>" +
            "    	<transition event=\"received2\" target=\"done\" />" +
            "    </state>" +
            "  </state>" +
            "  <final id=\"done\" />" +
            "</scxml>";

            // parse and interpret
            Interpreter interpreter = Interpreter.fromXML(xml, "");
            interpreter.interpret();

        }

        public static void testIOProcessor()
        {
            Console.WriteLine("testIOProcessor");
            CustomIOProc ioproc = new CustomIOProc();
            // just register prototype at global factory
            Factory.getInstance().registerIOProcessor(ioproc);

            String xml =
            "<scxml>" +
            "  <state id=\"s1\">" +
            "    <onentry>" +
            "      <send type=\"custom\">" +
            "        <content>This is some content!</content>" +
            "      </send>" +
            "    </onentry>" +
            "    <transition event=\"received1\" target=\"s2\" />" +
            "  </state>" +
            "  <state id=\"s2\">" +
            "    <onentry>" +
            "      <send type=\"custom\">" +
            "        <param name=\"foo\" expr=\"bar\" />" +
            "      </send>" +
            "    </onentry>" +
            "    <transition event=\"received2\" target=\"s3\" />" +
            "  </state>" +
            "  <state id=\"s3\">" +
            "    <onentry>" +
            "      <send type=\"custom\">" +
            "        <content>" +
            "        <this><is><xml/></is></this>" +
            "        </content>" +
            "      </send>" +
            "    </onentry>" +
            "    <transition event=\"received3\" target=\"done\" />" +
            "  </state>" +
            "  <final id=\"done\" />" +
            "</scxml>";

            // parse and interpret
            Interpreter interpreter = Interpreter.fromXML(xml, "");
            interpreter.interpret();

        }

        public static void testExecutableContent()
        {
            Console.WriteLine("testExecutableContent");
            CustomExecutableContent execContent = new CustomExecutableContent();
            Factory.getInstance().registerExecutableContent(execContent);

            Interpreter interpreter = Interpreter.fromXML(
                            "<scxml>\n" +
                            "  <state id=\"s0\">\n" +
                            "    <onentry>\n" +
                            "      <!-- custom foo=\"bar\">\n" +
                            "        <something></something>\n" +
                            "      </custom>\n" +
                            "      <custom foo=\"bar\">\n" +
                            "        <something></something>\n" +
                            "      </custom -->\n" +
                            "    </onentry>\n" +
                            "    <transition target=\"exit\" />" +
                            "  </state>\n" +
                            "  <final id=\"exit\" />" +
                            "</scxml>\n", ""
                    );
            interpreter.interpret();
            interpreter.Dispose();
        }

        public static void testLifeCycle()
        {
            Console.WriteLine("testLifeCycle");
            // syntactic xml parse error -> throws
            try
            {
                String xml = "<invalid";
                Interpreter interpreter = Interpreter.fromXML(xml, "");
                Debug.Assert(false);
            }
            catch (InterpreterException e)
            {
//                Console.WriteLine(e);
            }

            // semantic xml parse error -> throws
            try
            {
                String xml = "<invalid />";
                Interpreter interpreter = Interpreter.fromXML(xml, "");
                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                interpreter.step();
                Debug.Assert(false);
            }
            catch (InterpreterException e)
            {
//                Console.WriteLine(e);
            }

            // request unknown datamodel
            try
            {
                string xml =
                "<scxml datamodel=\"invalid\">" +
                "	<state id=\"start\">" +
                "		<transition target=\"done\" />" +
                " </state>" +
                " <final id=\"done\" />" +
                "</scxml>";
                Interpreter interpreter = Interpreter.fromXML(xml, "");
                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                interpreter.step();
                Debug.Assert(false);
            }
            catch (InterpreterException e)
            {
//                Console.WriteLine(e);
            }


            try
            {
                // two microsteps
                string xml =
                "<scxml>" +
                "	<state id=\"start\">" +
                "		<transition target=\"s2\" />" +
                "   </state>" +
                "	<state id=\"s2\">" +
                "		<transition target=\"done\" />" +
                " </state>" +
                " <final id=\"done\" />" +
                "</scxml>";

                Interpreter interpreter = Interpreter.fromXML(xml, "");

                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_MICROSTEPPED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_MICROSTEPPED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_FINISHED);

            }
            catch (InterpreterException e)
            {
                Console.WriteLine(e);
            }


            try
            {
                // single macrostep, multiple runs
                string xml =
                "<scxml>" +
                "	<state id=\"start\">" +
                "		<transition target=\"done\" />" +
                " </state>" +
                " <final id=\"done\" />" +
                "</scxml>";

                Interpreter interpreter = Interpreter.fromXML(xml, "");
                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_MICROSTEPPED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_FINISHED);
                interpreter.reset();

                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_MICROSTEPPED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_FINISHED);

            }
            catch (InterpreterException e)
            {
                Console.WriteLine(e);
            }


            try
            {
                // macrostep in between
                string xml =
                "<scxml>" +
                "	<state id=\"start\">" +
                "		<onentry>" +
                "			<send event=\"continue\" delay=\"2s\"/>" +
                "		</onentry>" +
                "		<transition target=\"s2\" event=\"continue\" />" +
                " </state>" +
                "	<state id=\"s2\">" +
                "		<transition target=\"done\" />" +
                " </state>" +
                " <final id=\"done\" />" +
                "</scxml>";

                Interpreter interpreter = Interpreter.fromXML(xml, "");
                Debug.Assert(interpreter.getState() == InterpreterState.USCXML_INSTANTIATED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_IDLE);
                Debug.Assert(interpreter.step(true) == InterpreterState.USCXML_MACROSTEPPED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_MICROSTEPPED);
                Debug.Assert(interpreter.step() == InterpreterState.USCXML_FINISHED);

            }
            catch (InterpreterException e)
            {
                Console.WriteLine(e);
            }
        }

    }
}
