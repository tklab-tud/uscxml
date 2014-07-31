package org.uscxml.tests.ioprocessor.adhoc.console;

import java.awt.Frame;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;

import org.uscxml.Data;
import org.uscxml.Event;
import org.uscxml.IOProcessor;
import org.uscxml.SendRequest;
import org.uscxml.StringList;

public class ConsoleIOProc extends IOProcessor implements KeyListener {
	
	public ConsoleIOProc(Frame frame) {
		super();
		frame.addKeyListener(this);
	}
	
	/**  IOProcessor */
	@Override
	public StringList getNames() {
		StringList ss = new StringList();
		ss.add("console");
		return ss;
	}

	/**  IOProcessor */
	@Override
	public Data getDataModelVariables() {
		// return anything for _ioprocessor['console']
		Data data = Data.fromJSON("{ foo: \"bar\", test: [1,2,3,4,5,6] }");
		return data;
	}

	/**  IOProcessor */
	@Override
	public void send(SendRequest req) {
		// interpreter wants to send something, just print on console
		System.out.println(req);
	}
	
	/**  KeyListener */
	@Override
	public void keyPressed(KeyEvent e) {
		Event evt = new Event("key.pressed");
		evt.setData(keyEventToData(e));
		returnEvent(evt, true);
	}

	/**  KeyListener */
	@Override
	public void keyReleased(KeyEvent e) {
		Event evt = new Event("key.released");
		evt.setData(keyEventToData(e));
		returnEvent(evt, true);
	}

	/**  KeyListener */
	@Override
	public void keyTyped(KeyEvent e) {
		Event evt = new Event("key.typed");
		evt.setData(keyEventToData(e));
		returnEvent(evt, true);
	}
	
	static Data keyEventToData(KeyEvent e) {
		Data data = new Data();
		data.put("id", new Data(e.getID()));
		data.put("keyChar", new Data(e.getKeyChar()));
		data.put("keyLocation", new Data(e.getKeyLocation()));
		data.put("modifiers", new Data(e.getModifiers()));
		data.put("modifiersEx", new Data(e.getModifiersEx()));
		data.put("when", new Data(e.getWhen()));
		data.put("actionKey", new Data(e.isActionKey()));
		data.put("altDown", new Data(e.isAltDown()));
		data.put("altGraphDown", new Data(e.isAltGraphDown()));
		data.put("ctrlDown", new Data(e.isControlDown()));
		data.put("metaDown", new Data(e.isMetaDown()));
		data.put("shiftDown", new Data(e.isShiftDown()));
		
		return data;
	}
}