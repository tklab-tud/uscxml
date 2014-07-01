package org.uscxml.datamodel.ecmascript;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.mozilla.javascript.Scriptable;
import org.uscxml.Data;
import org.uscxml.Event;

public class ECMAEvent implements Scriptable {

	protected Event event;
    protected Scriptable parent;
    protected Scriptable prototype;

    protected Map<String, Object> members = new HashMap<String, Object>();
    
	public ECMAEvent(Event event) {
		this.event = event;

		// copy event params to data
		Data data = event.getData();
		Map<String, List<Data>> params = event.getParams();
		for (String key : params.keySet()) {
			for (Data param : params.get(key)) {
				data.put(key, param);
			}
		}

		members.put("type", event.getEventType());
		members.put("data", new ECMAData(data));
		members.put("sendid", event.getSendId());
		members.put("origin", event.getOrigin());
		members.put("originType", event.getOriginType());
		// add others as necessary
		
	}

	@Override
	public String getClassName() {
		return "Event";
	}

	@Override
	public Object get(String name, Scriptable start) {
		if (members.containsKey(name))
			return members.get(name);
        return NOT_FOUND;
	}

	@Override
	public Object get(int index, Scriptable start) {
        return NOT_FOUND;
	}

	@Override
	public boolean has(String name, Scriptable start) {
        return (members.containsKey(name));
	}

	@Override
	public boolean has(int index, Scriptable start) {
		return false;
	}

	@Override
	public void put(String name, Scriptable start, Object value) {
	}

	@Override
	public void put(int index, Scriptable start, Object value) {
	}

	@Override
	public void delete(String name) {
	}

	@Override
	public void delete(int index) {
	}

	@Override
	public Scriptable getPrototype() {
		return prototype;
	}

	@Override
	public void setPrototype(Scriptable prototype) {
		this.prototype = prototype;
	}

	@Override
	public Scriptable getParentScope() {
		return parent;
	}

	@Override
	public void setParentScope(Scriptable parent) {
		this.parent = parent;
	}

	@Override
	public Object[] getIds() {
		return members.keySet().toArray();
	}

	@Override
	public Object getDefaultValue(Class<?> hint) {
        return "[object Event]";
	}

	@Override
	public boolean hasInstance(Scriptable instance) {
        Scriptable proto = instance.getPrototype();
        while (proto != null) {
            if (proto.equals(this))
                return true;
            proto = proto.getPrototype();
        }

        return false;
	}

}
