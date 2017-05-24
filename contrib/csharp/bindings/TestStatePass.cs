using System;
using System.Runtime.InteropServices;

namespace uscxml_test {
	using org.uscxml;
	
	class TestStatePass
	{
		[DllImport("kernel32.dll", CharSet = CharSet.Auto)]
		private static extern void SetDllDirectory(string lpPathName);

		[STAThread]
		static void Main(string[] args) {

			if (args.Length < 1) {
				System.Console.WriteLine("Expected SCXML filename and optional dllPath as arguments");
				Environment.Exit(-1);
			}

			try {
				if (args.Length > 1)
					SetDllDirectory(args[1]);
			} catch (System.EntryPointNotFoundException) {}

			Interpreter sc = Interpreter.fromURL(args[0]);
			while(sc.step() != InterpreterState.USCXML_FINISHED) {}
		}
	}
}
