package org.uscxml.tests.ioprocessor.console;

import java.awt.Frame;
import java.util.HashMap;
import java.util.Map;

import javax.swing.JLabel;
import javax.swing.JPanel;

import org.uscxml.Factory;
import org.uscxml.Interpreter;
import org.uscxml.InterpreterException;

public class ConsoleFrame extends Frame {
	
	private static final long serialVersionUID = 3682378173372160680L;
	public static Map<Interpreter, Frame> perInterpreter = new HashMap<Interpreter, Frame>();
	
	public ConsoleFrame() throws InterpreterException {
        super("Input Frame");
        JPanel p = new JPanel();
        JLabel label = new JLabel("Key Listener!");
        p.add(label);
        add(p);
        setSize(200, 100);
        
		final Interpreter interpreter = Interpreter.fromXML(
				  "<scxml datamodel=\"ecmascript\">"
			    + "	<script src=\"http://uscxml.tk.informatik.tu-darmstadt.de/scripts/dump.js\" />"
			    + " <script>var charSeq = \"\";</script>"
				+ "	<state id=\"idle\">"
				+ "   <transition event=\"key.released\" cond=\"_event.data.keyChar == 10\">"
				+ "		<log expr=\"charSeq\" />"
				+ "     <script>"
				+ "       charSeq = \"\";"
				+ "     </script>"
				+ "   </transition>"
				+ "   <transition event=\"*\">"
				+ "     <log label=\"event\" expr=\"dump(_event.data)\" />"
				+ "     <script>charSeq += String.fromCharCode(_event.data.keyChar);</script>"
				+ "   </transition>"
				+ "	</state>"
				+ "</scxml>");


		perInterpreter.put(interpreter, this);
		
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

        setVisible(true);
	}
	
	public static void main(String[] args) throws InterpreterException {
		System.load("/Users/sradomski/Documents/TK/Code/uscxml/build/cli/lib/libuscxmlNativeJava64.jnilib");

		ConsoleIOProc ioProc = new ConsoleIOProc();
		Factory.getInstance().registerIOProcessor(ioProc);
		
		ConsoleFrame frame = new ConsoleFrame();
		
	}

}

