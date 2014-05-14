package org.uscxml.datamodel.ecmascript;

import org.mozilla.javascript.Callable;
import org.mozilla.javascript.Context;
import org.mozilla.javascript.NativeJSON;
import org.mozilla.javascript.Scriptable;
import org.mozilla.javascript.ScriptableObject;
import org.mozilla.javascript.Undefined;
import org.uscxml.Data;
import org.uscxml.DataNative;
import org.uscxml.Event;
import org.uscxml.Interpreter;
import org.uscxml.JavaDataModel;
import org.uscxml.StringSet;
import org.uscxml.StringVector;

public class ECMAScriptDataModel extends JavaDataModel {

	private class NullCallable implements Callable {
		@Override
		public Object call(Context context, Scriptable scope,
				Scriptable holdable, Object[] objects) {
			return objects[1];
		}
	}

	public Context ctx;
	public Scriptable scope;

	public Data getScriptableAsData(Object object) {
		Data data = new Data();

		Scriptable s;
		try {
			s = (Scriptable) object;
			String className = s.getClassName(); // ECMA class name
			if (className.toLowerCase().equals("object")) {
				ScriptableObject obj = (ScriptableObject) Context.toObject(s,
						scope);
				for (Object key : obj.getIds()) {
					data.compound.put(Context.toString(key),
							getScriptableAsData(obj.get(key)));
				}
			}
		} catch (ClassCastException e) {
			if (object instanceof Boolean) {
				data.atom = (Context.toBoolean(object) ? "true" : "false");
				data.type = Data.Type.INTERPRETED;
			} else if (object instanceof String) {
				data.atom = (String) object;
				data.type = Data.Type.VERBATIM;
			} else if (object instanceof Integer) {
				data.atom = ((Integer) object).toString();
				data.type = Data.Type.INTERPRETED;
			} else {
				throw new RuntimeException("Unhandled ECMA type "
						+ object.getClass().getName());
			}
		}

		return data;
	}

	public ScriptableObject getDataAsScriptable(Data data) {
		throw new UnsupportedOperationException("Not implemented");
	}

	@Override
	public JavaDataModel create(Interpreter interpreter) {
		/**
		 * Called when an SCXML interpreter wants an instance of this datamodel
		 * Be careful to instantiate attributes of instance returned and not
		 * *this*
		 */
		ECMAScriptDataModel newDM = new ECMAScriptDataModel();
		newDM.ctx = Context.enter();

		Data ioProcs = new Data();
		StringVector keys = interpreter.getIOProcessorKeys();
		for (int i = 0; i < keys.size(); i++) {
			ioProcs.compound.put(keys.get(i), new Data(interpreter.getIOProcessors().get(keys.get(i)).getDataModelVariables()));
		}
		
		try {
			newDM.scope = newDM.ctx.initStandardObjects();
			newDM.scope.put("_ioprocessors", newDM.scope, new ECMAData(ioProcs));
		} catch (Exception e) {
			System.err.println(e);
		}

		return newDM;
	}

	@Override
	public StringSet getNames() {
		/**
		 * Register with the following names for the datamodel attribute at the
		 * scxml element. <scxml datamodel="one of these">
		 */
		StringSet ss = new StringSet();
		ss.insert("ecmascript");
		return ss;
	}

	@Override
	public boolean validate(String location, String schema) {
		/**
		 * Validate the datamodel. This make more sense for XML datamodels and
		 * is pretty much unused but required as per draft.
		 */
		return true;
	}

	@Override
	public void setEvent(Event event) {
		/**
		 * Make the current event available as the variable _event in the
		 * datamodel.
		 */
		ECMAEvent ecmaEvent = new ECMAEvent(event);		
		scope.put("_event", scope, ecmaEvent);
	}

	@Override
	public DataNative getStringAsData(String content) {
		/**
		 * Evaluate the string as a value expression and transform it into a
		 * JSON-like Data structure
		 */
		if (content.length() == 0) {
			return Data.toNative(new Data());
		}

		// is it a json expression?
		try {
			Object json = NativeJSON.parse(ctx, scope, content,
					new NullCallable());
			if (json != NativeJSON.NOT_FOUND) {
				return Data.toNative(getScriptableAsData(json));
			}
		} catch (org.mozilla.javascript.EcmaError e) {
		}
		
		// is it a function call or variable?
		Object x = ctx.evaluateString(scope, content, "uscxml", 0, null);
		if (x == Undefined.instance) {
			// maybe a literal string?
			x = ctx.evaluateString(scope, '"' + content + '"', "uscxml", 0,
					null);
		}
		return Data.toNative(getScriptableAsData(x));
	}

	@Override
	public long getLength(String expr) {
		/**
		 * Return the length of the expression if it were an array, used by
		 * foreach element.
		 */

		Object x = scope.get(expr, scope);
		if (x == Undefined.instance) {
			return 0;
		}

		Scriptable result = Context.toObject(x, scope);
		if (result.has("length", result)) {
			return (long) Context.toNumber(result.get("length", result));
		}
		return 0;
	}

	@Override
	public void setForeach(String item, String array, String index,
			long iteration) {
		/**
		 * Prepare an iteration of the foreach element, by setting the variable
		 * in index to the current iteration and setting the variable in item to
		 * the current item from array.
		 */

		try {
			// get the array object
			Scriptable arr = (Scriptable) scope.get(array, scope);

			if (arr.has((int) iteration, arr)) {
				ctx.evaluateString(scope, item + '=' + array + '[' + iteration
						+ ']', "uscxml", 1, null);
				if (index.length() > 0) {
					ctx.evaluateString(scope, index + '=' + iteration,
							"uscxml", 1, null);
				}
			} else {
				// we ought to throw a error.execution
			}

		} catch (ClassCastException e) {
			System.err.println(e);
		}
	}

	@Override
	public void eval(String scriptElem, String expr) {
		/**
		 * Evaluate the given expression in the datamodel. This is used foremost
		 * with script elements.
		 */
		ctx.evaluateString(scope, expr, "uscxml", 1, null);

	}

	@Override
	public String evalAsString(String expr) {
		/**
		 * Evaluate the expression as a string e.g. for the log element.
		 */
		Object result = ctx.evaluateString(scope, expr, "uscxml", 1, null);
		return Context.toString(result);
	}

	@Override
	public boolean evalAsBool(String elem, String expr) {
		/**
		 * Evaluate the expression as a boolean for cond attributes in if and
		 * transition elements.
		 */
		Object result = ctx.evaluateString(scope, expr, "uscxml", 1, null);
		return Context.toBoolean(result);
	}

	@Override
	public boolean isDeclared(String expr) {
		/**
		 * The interpreter is supposed to raise an error if we assign to an
		 * undeclared variable. This method is used to check whether a location
		 * from assign is declared.
		 */
		Object x = scope.get(expr, scope);
		return x != Scriptable.NOT_FOUND;
	}

	@Override
	public void init(String dataElem, String location, String content) {
		/**
		 * Called when we pass data elements.
		 */
		if (("null").equals(location))
			return;

		if (("null").equals(content) || content.length() == 0) {
			scope.put(location, scope, Context.getUndefinedValue());
			return;
		}

		try {
			Object json = NativeJSON.parse(ctx, scope, content,
					new NullCallable());
			if (json != NativeJSON.NOT_FOUND) {
				scope.put(location, scope, json);
			} else {
				scope.put(location, scope, content);
			}
		} catch (org.mozilla.javascript.EcmaError e) {
			scope.put(location, scope, content);
		}
	}

	@Override
	public void assign(String assignElem, String location, String content) {
		/**
		 * Called when we evaluate assign elements
		 */
		if (("null").equals(location))
			return;

		if (("null").equals(content) || content.length() == 0) {
			scope.put(location, scope, Context.getUndefinedValue());
			return;
		}

		String expr = location + "=" + content;
		ctx.evaluateString(scope, expr, "uscxml", 1, null);		
	}

}
