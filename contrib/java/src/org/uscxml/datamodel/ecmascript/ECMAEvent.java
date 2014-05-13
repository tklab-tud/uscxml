package org.uscxml.datamodel.ecmascript;

import org.mozilla.javascript.ScriptableObject;
import org.mozilla.javascript.annotations.JSConstructor;
import org.mozilla.javascript.annotations.JSGetter;
import org.uscxml.Data;
import org.uscxml.DataMap;
import org.uscxml.Event;
import org.uscxml.Event.Type;

public class ECMAEvent {

	private Event event;

	private static final long serialVersionUID = -5241020609349204355L;

	public ECMAEvent(Event event) {
		this.event = event;
	}

	public String getName() {
		return event.getName();
	}

	public Type getEventType() {
		return event.getEventType();
	}

	public String getOrigin() {
		return event.getOrigin();
	}

	public String getOriginType() {
		return event.getOriginType();
	}

	public String getContent() {
		return event.getContent();
	}

	public String getXML() {
		return event.getXML();
	}

	public String getSendId() {
		return event.getSendId();
	}

	public String getInvokeId() {
		return event.getInvokeId();
	}

	public Data getData() {
		return new Data(event.getData());
	}

	public DataMap getNameList() {
		return event.getNameList();
	}

	/*
	@JSGetter
	public SWIGTYPE_p_std__multimapT_std__string_uscxml__Data_t getParams() {
		// TODO Auto-generated method stub
		return super.getParams();
	}
*/
	
}
