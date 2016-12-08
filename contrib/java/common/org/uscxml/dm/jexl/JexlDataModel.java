package org.uscxml.dm.jexl;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.jexl3.JexlBuilder;
import org.apache.commons.jexl3.JexlEngine;
import org.apache.commons.jexl3.JexlException;
import org.apache.commons.jexl3.JexlExpression;
import org.apache.commons.jexl3.MapContext;
import org.uscxml.Data;
import org.uscxml.DataList;
import org.uscxml.DataMap;
import org.uscxml.DataModel;
import org.uscxml.DataModelExtension;
import org.uscxml.ErrorEvent;
import org.uscxml.Event;
import org.uscxml.StringList;
import org.uscxml.StringVector;

public class JexlDataModel extends DataModel {

	protected static final JexlEngine jexl = new JexlBuilder().cache(512).strict(true).silent(false).create();
	public MapContext ctx = new MapContext();

	@Override
	public void addExtension(DataModelExtension ext) {
		throw new UnsupportedOperationException("Cannot add extensions to the jexl datamodel");
	}

	@Override
	public StringList getNames() {
		StringList names = new StringList();
		names.add("jexl");
		return names;
	}
	
	@Override
	public DataModel create() {
		JexlDataModel dm = new JexlDataModel();		
		return dm;
	}

	@Override
	public boolean isValidSyntax(String expr) {
		try {
			jexl.createExpression(expr);
			return true;
		} catch(JexlException e) {
			return false;
		}
	}

	@Override
	public void setEvent(Event event) {
		ctx.set("_event", event);
	}

	@Override
	public Data getAsData(String content) {
		try {
			JexlExpression ex = jexl.createExpression(content);
			return getJexlObjectAsData(ex.evaluate(ctx));
		} catch(Exception e) {
		}
		return null;
	}

	@Override
	public Data evalAsData(String content) {
		JexlExpression expr = jexl.createExpression(content);
		Data d = getJexlObjectAsData(expr.evaluate(ctx));
		return d;
	}

	@Override
	public boolean evalAsBool(String expr) {
		try {
			JexlExpression ex = jexl.createExpression("!!" + expr);
			Object result = ex.evaluate(ctx);
			return (Boolean) result;
		} catch(Exception e) {
			e.printStackTrace();
		}
		return false;
	}

	@Override
	public long getLength(String expr) {
		try {
			JexlExpression ex = jexl.createExpression(expr);
			Object res = ex.evaluate(ctx);

			return Array.getLength(res);

		} catch(Exception e) {
			throw new ErrorEvent("Cannot evaluate '" + expr + "' as an array: " + e.getMessage());
		}
	}

	@Override
	public void setForeach(String item, String array, String index, long iteration) {
		Object res = null;
		try {
			JexlExpression ex = jexl.createExpression(array);
			res = ex.evaluate(ctx);
		} catch(Exception e) {
			throw new ErrorEvent("Cannot evaluate '" + array + "' as an array: " + e.getMessage());
		}
		try {
			JexlExpression ex = jexl.createExpression(item + "==" + item + ";");
			ex.evaluate(ctx);

			ctx.set(item, Array.get(res, (int) iteration));
		} catch(Exception e) {
			throw new ErrorEvent("Cannot set item '" + item + "' to current item: " + e.getMessage());
		}
		try {
			if (index.length() > 0) {
				ctx.set(index, iteration);
			}
		} catch(Exception e) {
			throw new ErrorEvent("Cannot set index '" + index + "' to current index: " + e.getMessage());
		}
	}

	@Override
	public void assign(String location, Data data) {
		try {
			ctx.set(location, getDataAsJexlObject(data));
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	@Override
	public void init(String location, Data data) {
		ctx.set(location, null);
		assign(location, data);
	}

	@Override
	public boolean isDeclared(String expr) {
		try {
			JexlExpression ex = jexl.createExpression(expr);
			Object result = ex.evaluate(ctx);
			return (Boolean) result;
		} catch(JexlException e) {
		}
		return false;
	}
	
	protected Object evalAsObject(String expr) {
		try {
			JexlExpression ex = jexl.createExpression(expr);
			return (ex.evaluate(ctx));
		} catch(JexlException e) {
		}
		return null;
	}
	
	protected Data getJexlObjectAsData(Object obj) {
		Data d = new Data();
		if (obj.getClass().isArray()) {
		    int length = Array.getLength(obj);
		    for (int i = 0; i < length; i ++) {
		        d.getArray().add(getJexlObjectAsData(Array.get(obj, i)));
		    }
		} else if (obj.getClass().isPrimitive() || isWrapperType(obj.getClass())) {
			String val = obj.toString();
			try {
				Integer.parseInt(obj.toString());
				d.setAtom(obj.toString());
				d.setType(Data.Type.INTERPRETED);
				return d;
			} catch(NumberFormatException e) {}
			try {
				Double.parseDouble(obj.toString());
				d.setAtom(obj.toString());
				d.setType(Data.Type.INTERPRETED);
				return d;
			} catch(NumberFormatException e) {}
			d.setAtom(obj.toString());
			d.setType(Data.Type.VERBATIM);
			return d;
		} else {
			Field[] fields = obj.getClass().getDeclaredFields();
			for (Field field: fields) {
				Object newObj = null;
				try {
					field.get(newObj);
					d.getCompound().set(field.getName(), getJexlObjectAsData(newObj));
				} 
				catch (IllegalArgumentException e) {}
				catch (IllegalAccessException e) {}
			}
			return d;
		}

		return d;
	}
	
	protected Object getDataAsJexlObject(Data data) {
		if (data.getAtom().length() > 0) {
			if (data.getType() == Data.Type.INTERPRETED) {
				try {
					JexlExpression exp = jexl.createExpression(data.getAtom());
					return exp.evaluate(ctx);
				} catch (Exception e) {
					e.printStackTrace();
				}
				return new String(data.getAtom());
			}
			try {
				JexlExpression exp = jexl.createExpression(data.getAtom());
				return exp.evaluate(ctx);
			} catch (Exception e) {
			}
			return new String("\"" + data.getAtom() + "\"");

		} else if (data.getCompound().size() > 0) {
			StringVector keys = data.getCompoundKeys();
			DataMap dataCompound = data.getCompound();
			Map<String, Object> objCompound = new HashMap<String, Object>();
			for (int i = 0; i < keys.size(); i++) {
				objCompound.put(keys.get(i), getDataAsJexlObject(dataCompound.get(keys.get(i))));
			}
			return objCompound;
		} else if (data.getArray().size() > 0) {
			DataList dataList = data.getArray();
			List<Object> objList = new ArrayList<Object>((int) data.getArray().size());
			for (int i = 0; i < dataList.size(); i++) {
				objList.add(i, getDataAsJexlObject(dataList.get(i)));
			}
			return objList;
		}
		return new Object();
	}
	
    protected static boolean isWrapperType(Class<?> clazz) {
        return WRAPPER_TYPES.contains(clazz);
    }

    private static final Set<Class<?>> WRAPPER_TYPES = getWrapperTypes();

    private static Set<Class<?>> getWrapperTypes() {
        Set<Class<?>> ret = new HashSet<Class<?>>();
        ret.add(String.class);
        ret.add(Boolean.class);
        ret.add(Character.class);
        ret.add(Byte.class);
        ret.add(Short.class);
        ret.add(Integer.class);
        ret.add(Long.class);
        ret.add(Float.class);
        ret.add(Double.class);
        ret.add(Void.class);
        return ret;
    }

}
