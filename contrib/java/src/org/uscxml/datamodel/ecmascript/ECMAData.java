package org.uscxml.datamodel.ecmascript;

import org.mozilla.javascript.Scriptable;
import org.uscxml.Data;

public class ECMAData implements Scriptable {

	protected Data data;
    protected Scriptable parent;
    protected Scriptable prototype;

	public ECMAData(Data data) {
		this.data = data;
	}

	@Override
	public String getClassName() {
		return "Data";
	}

	public Object unwrap(Data data) {
		if (data.atom.length() > 0) {
			return data.atom;
		}
		return new ECMAData(data);
		
	}
	
	@Override
	public Object get(String name, Scriptable start) {
		if (data.compound.containsKey(name))
			return unwrap(data.compound.get(name));
		return NOT_FOUND;
	}

	@Override
	public Object get(int index, Scriptable start) {
		if (data.array.size() > index)
			return unwrap(data.array.get(index));
		return NOT_FOUND;
	}

	@Override
	public boolean has(String name, Scriptable start) {
		return data.compound.containsKey(name);
	}

	@Override
	public boolean has(int index, Scriptable start) {
		return data.array.size() > index;
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
		return data.compound.keySet().toArray();
	}

	@Override
	public Object getDefaultValue(Class<?> hint) {
        return "[object Data]";
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
