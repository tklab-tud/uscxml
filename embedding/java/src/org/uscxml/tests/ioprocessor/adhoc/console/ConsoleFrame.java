package org.uscxml.tests.ioprocessor.adhoc.console;

import java.awt.Frame;

import javax.swing.JLabel;
import javax.swing.JPanel;

import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;

public class ConsoleFrame extends Frame {
	private static final long serialVersionUID = 3682378173372160680L;
	private ConsoleIOProc ioProc;

	public ConsoleFrame() throws InterpreterException {
		super("Input Frame");
		JPanel p = new JPanel();
		JLabel label = new JLabel("Key Listener!");
		p.add(label);
		add(p);
		setSize(200, 100);

		// instantiate SCXML interpreter
		final Interpreter interpreter = Interpreter.fromXML(
				"<scxml datamodel=\"ecmascript\">"
						+ "	<script src=\"http://uscxml.tk.informatik.tu-darmstadt.de/scripts/dump.js\" />"
						+ " <script>var charSeq = \"\";</script>"
						+ "	<state id=\"idle\">"
						+ "   <transition event=\"error\" target=\"quit\">"
						+ "     <log label=\"error\" expr=\"dump(_event)\" />"
						+ "   </transition>"
						+ "   <transition event=\"key.released\" cond=\"_event.data.keyChar == 10\">"
						+ "     <send type=\"console\">"
						+ "       <param name=\"foo\" expr=\"charSeq\" />"
						+ "     </send>"
						+ "     <script>"
						+ "       charSeq = \"\"; // reset string"
						+ "     </script>"
						+ "   </transition>"
						+ "   <transition event=\"*\">"
						+ "     <log label=\"event\" expr=\"dump(_event.data)\" />"
						+ "     <script>charSeq += String.fromCharCode(_event.data.keyChar);</script>"
						+ "   </transition>"
						+ "	</state>"
						+ " <final id=\"quit\" />"
						+ "</scxml>");

		/**
		 *  ConsoleIOProc will register as a keyboard listener and send events to the interpreter.
		 *  
		 *   This circumvents the factory and registers instances directly. You will have to promise
		 *   that the ioProc instance exists for the complete lifetime of the interpreter, otherwise
		 *   finalize() will call the C++ destructor and SegFaults will occur.
		 */
		ioProc = new ConsoleIOProc(this);
		interpreter.addIOProcessor(ioProc);

		// Start the interpreter in a separate thread
		Thread intrerpreterThread = new Thread(new Runnable() {
			@Override
			public void run() {
				try {
					interpreter.interpret();
				} catch (InterpreterException e) {
					e.printStackTrace();
				}				
			}
		});
		intrerpreterThread.start();		

		// show the user interface
		setVisible(true);
	}
	
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");
		ConsoleFrame frame = new ConsoleFrame();
	}
}
