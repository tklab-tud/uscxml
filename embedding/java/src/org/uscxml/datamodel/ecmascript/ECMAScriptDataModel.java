package org.uscxml.datamodel.ecmascript;

import java.lang.reflect.Method;
import java.util.Map;

import org.mozilla.javascript.Callable;
import org.mozilla.javascript.Context;
import org.mozilla.javascript.EvaluatorException;
import org.mozilla.javascript.FunctionObject;
import org.mozilla.javascript.NativeJSON;
import org.mozilla.javascript.Scriptable;
import org.mozilla.javascript.ScriptableObject;
import org.mozilla.javascript.Undefined;
import org.uscxml.Data;
import org.uscxml.DataModel;
import org.uscxml.Event;
import org.uscxml.Interpreter;
import org.uscxml.NativeIOProcessor;
import org.uscxml.NativeInvoker;
import org.uscxml.StringList;

public class ECMAScriptDataModel extends DataModel {

	public static boolean debug = true;
	
	private class NullCallable implements Callable {
		@Override
		public Object call(Context context, Scriptable scope,
				Scriptable holdable, Object[] objects) {
			return objects[1];
		}
	}

	public Context ctx;
	public Scriptable scope;
	public Interpreter interpreter;

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
					data.put(Context.toString(key),
							getScriptableAsData(obj.get(key)));
				}
			}
		} catch (ClassCastException e) {
			if (object instanceof Boolean) {
				data.setAtom(Context.toBoolean(object) ? "true" : "false");
				data.setType(Data.Type.INTERPRETED);
			} else if (object instanceof String) {
				data.setAtom((String) object);
				data.setType(Data.Type.VERBATIM);
			} else if (object instanceof Integer) {
				data.setAtom(((Integer) object).toString());
				data.setType(Data.Type.INTERPRETED);
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

	public static boolean jsIn(String stateName) {
		return true;
	}

	@Override
	public DataModel create(Interpreter interpreter) {
		/**
		 * Called when an SCXML interpreter wants an instance of this datamodel
		 * Be careful to instantiate attributes of instance returned and not
		 * *this*
		 */
		
		ECMAScriptDataModel newDM = new ECMAScriptDataModel();
		newDM.swigReleaseOwnership();
		newDM.interpreter = interpreter;
		newDM.ctx = Context.enter();

		try {
			newDM.scope = newDM.ctx.initStandardObjects();
		} catch (Exception e) {
			System.err.println(e);
		}

		newDM.scope.put("_name", newDM.scope, interpreter.getName());
		newDM.scope.put("_sessionid", newDM.scope, interpreter.getSessionId());

		// ioProcessors
		{
			Data ioProcs = new Data();
			Map<String, NativeIOProcessor> ioProcNatives = interpreter.getIOProcessors();
			for (String key : ioProcNatives.keySet()) {
				ioProcs.put(key, ioProcNatives.get(key).getDataModelVariables());
			}
			newDM.scope
					.put("_ioprocessors", newDM.scope, new ECMAData(ioProcs));
		}

		// invokers
		{
			Data invokers = new Data();
			Map<String, NativeInvoker> invokersNatives = interpreter.getInvokers();
			for (String key : invokersNatives.keySet()) {
				invokers.put(key, invokersNatives.get(key).getDataModelVariables());
			}
			newDM.scope
					.put("_ioprocessors", newDM.scope, new ECMAData(invokers));
		}
		
		// In predicate (not working as static is required) see:
		// http://stackoverflow.com/questions/3441947/how-do-i-call-a-method-of-a-java-instance-from-javascript/16479685#16479685
		try {
			Class[] parameters = new Class[] { String.class };
			Method inMethod = ECMAScriptDataModel.class.getMethod("jsIn",
					parameters);
			FunctionObject inFunc = new FunctionObject("In", inMethod,
					newDM.scope);
			newDM.scope.put("In", newDM.scope, inFunc);
		} catch (SecurityException e) {
			System.err.println(e);
		} catch (NoSuchMethodException e) {
			System.err.println(e);
		}

		return newDM;
	}

	@Override
	public StringList getNames() {
		/**
		 * Register with the following names for the datamodel attribute at the
		 * scxml element. <scxml datamodel="one of these">
		 */
		StringList ss = new StringList();
		ss.add("ecmascript");
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
		if (debug) {
			System.out.println(interpreter.getName() + " setEvent");
		}
		
		/**
		 * Make the current event available as the variable _event in the
		 * datamodel.
		 */
		ECMAEvent ecmaEvent = new ECMAEvent(event);
		scope.put("_event", scope, ecmaEvent);
	}

	@Override
	public Data getStringAsData(String content) {
		if (debug) {
			System.out.println(interpreter.getName() + " getStringAsData");
		}

		/**
		 * Evaluate the string as a value expression and transform it into a
		 * JSON-like Data structure
		 */
		if (content.length() == 0) {
			return new Data();
		}

		// is it a json expression?
		try {
			Object json = NativeJSON.parse(ctx, scope, content,
					new NullCallable());
			if (json != NativeJSON.NOT_FOUND) {
				return getScriptableAsData(json);
			}
		} catch (org.mozilla.javascript.EcmaError e) {
			System.err.println(e);
		}

		// is it a function call or variable?
		Object x = ctx.evaluateString(scope, content, "uscxml", 0, null);
		if (x == Undefined.instance) {
			// maybe a literal string?
			x = ctx.evaluateString(scope, '"' + content + '"', "uscxml", 0,
					null);
		}
		return getScriptableAsData(x);
	}

	@Override
	public long getLength(String expr) {
		if (debug) {
			System.out.println(interpreter.getName() + " getLength");
		}

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
		if (debug) {
			System.out.println(interpreter.getName() + " setForeach");
		}

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
				handleException("");
			}

		} catch (ClassCastException e) {
			System.err.println(e);
		}
	}

	@Override
	public void eval(String scriptElem, String expr) {
		if (debug) {
			System.out.println(interpreter.getName() + " eval");
		}

		/**
		 * Evaluate the given expression in the datamodel. This is used foremost
		 * with script elements.
		 */
		ctx.evaluateString(scope, expr, "uscxml", 1, null);

	}

	@Override
	public String evalAsString(String expr) {
		if (debug) {
			System.out.println(interpreter.getName() + " evalAsString: " + expr);
		}

		/**
		 * Evaluate the expression as a string e.g. for the log element.
		 */
		if (!ctx.stringIsCompilableUnit(expr)) {
			handleException("");
			return "";
		}
		try {
			Object result = ctx.evaluateString(scope, expr, "uscxml", 1, null);
			return Context.toString(result);
		} catch (IllegalStateException e) {
			System.err.println(e);
			handleException("");
		} catch (EvaluatorException e) {
			System.err.println(e);
			handleException("");
		}
		return "";
	}

	@Override
	public boolean evalAsBool(String elem, String expr) {
		if (debug) {
			System.out.println(interpreter.getName() + " evalAsBool");
		}

		/**
		 * Evaluate the expression as a boolean for cond attributes in if and
		 * transition elements.
		 */
		Object result = ctx.evaluateString(scope, expr, "uscxml", 1, null);
		return Context.toBoolean(result);
	}

	@Override
	public boolean isDeclared(String expr) {
		if (debug) {
			System.out.println(interpreter.getName() + " isDeclared");
		}

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
		if (debug) {
			System.out.println(interpreter.getName() + " init");
		}

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
		if (debug) {
			System.out.println(interpreter.getName() + " assign");
		}

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

	public void handleException(String cause) {
		Event exceptionEvent = new Event();
		exceptionEvent.setName("error.execution");
		exceptionEvent.setEventType(Event.Type.PLATFORM);

		interpreter.receiveInternal(exceptionEvent);
	}
}
