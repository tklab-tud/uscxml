%module(directors="1", allprotected="1") uscxmlNativeJava

// provide a macro for the header files
#define SWIGIMPORTED 1

%include <stl.i>
%include <std_map.i>
%include <std_string.i>
%include <inttypes.i>
%include "../stl_set.i"
%include "../stl_list.i"

%include <boost_shared_ptr.i>

// these are needed at least for the templates to work
typedef uscxml::Blob Blob;
typedef uscxml::Data Data;
typedef uscxml::Event Event;
typedef uscxml::InvokeRequest InvokeRequest;
typedef uscxml::SendRequest SendRequest;
typedef uscxml::Invoker Invoker;
typedef uscxml::IOProcessor IOProcessor;
typedef uscxml::DataModel DataModel;
typedef uscxml::ExecutableContent ExecutableContent;
typedef uscxml::InvokerImpl InvokerImpl;
typedef uscxml::IOProcessorImpl IOProcessorImpl;
typedef uscxml::DataModelImpl DataModelImpl;
typedef uscxml::ExecutableContentImpl ExecutableContentImpl;

%feature("director") uscxml::WrappedInvoker;
%feature("director") uscxml::WrappedDataModel;
%feature("director") uscxml::WrappedIOProcessor;
%feature("director") uscxml::WrappedExecutableContent;
%feature("director") uscxml::WrappedInterpreterMonitor;

// disable warning related to unknown base class
#pragma SWIG nowarn=401
// do not warn when we override symbols via extend
#pragma SWIG nowarn=302
// do not warn when ignoring overrided method
#pragma SWIG nowarn=516

%javaconst(1);

%rename(equals) operator==; // signature is wrong, still useful
%rename(isValid) operator bool;

//**************************************************
// This ends up in the generated wrapper code
//**************************************************

%{

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"
#include "../../../uscxml/concurrency/BlockingQueue.h"
#include "../../../uscxml/server/HTTPServer.h"
#include "../../../uscxml/debug/DebuggerServlet.h"

#include "../wrapped/WrappedInvoker.h"
#include "../wrapped/WrappedDataModel.h"
#include "../wrapped/WrappedExecutableContent.h"
#include "../wrapped/WrappedIOProcessor.h"
#include "../wrapped/WrappedInterpreterMonitor.h"

using namespace uscxml;
using namespace Arabica::DOM;

// the wrapped* C++ classes get rid of DOM nodes and provide more easily wrapped base classes
#include "../wrapped/WrappedInvoker.cpp"
#include "../wrapped/WrappedDataModel.cpp"
#include "../wrapped/WrappedExecutableContent.cpp"
#include "../wrapped/WrappedIOProcessor.cpp"
#include "../wrapped/WrappedInterpreterMonitor.cpp"

%}

%define WRAP_THROW_EXCEPTION( MATCH )
%javaexception("org.uscxml.InterpreterException") MATCH {
  try {
    $action
  }
  catch ( uscxml::Event& e ) {
    jclass eclass = jenv->FindClass("org/uscxml/InterpreterException");
    if ( eclass ) {
      std::stringstream ss;
      ss << std::endl << e;
      jenv->ThrowNew( eclass, ss.str().c_str() );
    }
  }
}
%enddef

WRAP_THROW_EXCEPTION(uscxml::Interpreter::fromXML);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::fromURI);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::step);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::interpret);


%define WRAP_HASHCODE( CLASSNAME )
%extend CLASSNAME {
	virtual int hashCode() {
/*		std::cout << "Calc hashcode as " << (int)(size_t)self->getImpl().get() << std::endl << std::flush;*/
		return (int)(size_t)self->getImpl().get();
	}
};
%enddef

%define WRAP_TO_STRING( CLASSNAME )
%extend CLASSNAME {
	virtual std::string toString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
};
%enddef

WRAP_TO_STRING(uscxml::Event);
WRAP_TO_STRING(uscxml::Data);
WRAP_TO_STRING(uscxml::SendRequest);
WRAP_TO_STRING(uscxml::InvokeRequest);

WRAP_HASHCODE(uscxml::Interpreter);

%include "../uscxml_ignores.i"

#if 0
// see http://swig.org/Doc2.0/Java.html#Java_date_marshalling
%define BEAUTIFY_NATIVE( MATCH, WRAPPER, NATIVE )

%rename WRAPPER NATIVE;

%typemap(jstype) const MATCH & "WRAPPER"
%typemap(jstype) MATCH "WRAPPER"

%typemap(javain,
         pre="    NATIVE temp$javainput = $javainput.toNative();", 
         pgcppname="temp$javainput") const MATCH &
         "$javaclassname.getCPtr(temp$javainput)"

 %typemap(javain,
          pre="    NATIVE temp$javainput = $javainput.toNative();", 
          pgcppname="temp$javainput") MATCH
          "$javaclassname.getCPtr(temp$javainput)"

%typemap(javaout) const MATCH & {
    NATIVE nativeData = new NATIVE($jnicall, $owner);
    return new WRAPPER(nativeData);
}

%typemap(javaout) MATCH {
    NATIVE nativeData = new NATIVE($jnicall, $owner);
    return new WRAPPER(nativeData);
}

%typemap(javadirectorout) MATCH "NATIVE.getCPtr($javacall.toNative())"

%typemap(javadirectorin) MATCH "WRAPPER.fromNative(new NATIVE($jniinput, false))";
%typemap(javadirectorin) const MATCH & "WRAPPER.fromNative(new NATIVE($jniinput, false))";

%typemap(directorin,descriptor="L/org/uscxml/"##"WRAPPER;") const MATCH & "*(MATCH **)&$input = (MATCH *) &$1;"

%typemap(directorout) MATCH ($&1_type argp)
%{ argp = *($&1_ltype*)&$input;
   if (!argp) {
     SWIG_JavaThrowException(jenv, SWIG_JavaNullPointerException, "Unexpected null return for type $1_type");
     return $null;
   }
   $result = *argp; %}

%enddef

/*
// not used as it will not work for directors :(
BEAUTIFY_NATIVE(uscxml::Data, Data, DataNative);
BEAUTIFY_NATIVE(uscxml::Event, Event, EventNative);
BEAUTIFY_NATIVE(uscxml::SendRequest, SendRequest, SendRequestNative);
BEAUTIFY_NATIVE(uscxml::InvokeRequest, InvokeRequest, InvokeRequestNative);
*/
#endif

// bytearray for Blob::data
// see: http://stackoverflow.com/questions/9934059/swig-technique-to-wrap-unsigned-binary-data

%apply (char *STRING, size_t LENGTH) { (const char* data, size_t size) };

%typemap(jni) char* getData "jbyteArray"
%typemap(jtype) char* getData "byte[]"
%typemap(jstype) char* getData "byte[]"
%typemap(javaout) char* getData {
  return $jnicall;
}

%typemap(out) char* getData {
  $result = JCALL1(NewByteArray, jenv, ((uscxml::Blob const *)arg1)->getSize());
  JCALL4(SetByteArrayRegion, jenv, $result, 0, ((uscxml::Blob const *)arg1)->getSize(), (jbyte *)$1);
}

//***********************************************
// Beautify important classes
//***********************************************

%javamethodmodifiers uscxml::Event::getParamMap() "private";
%javamethodmodifiers uscxml::Event::getParamMapKeys() "private";
%javamethodmodifiers uscxml::Event::setParamMap(const std::map<std::string, std::list<uscxml::Data> >&) "private";
%javamethodmodifiers uscxml::Event::getNameListKeys() "private";
%javamethodmodifiers uscxml::Interpreter::getIOProcessorKeys() "private";
%javamethodmodifiers uscxml::Interpreter::getInvokerKeys() "private";
%javamethodmodifiers uscxml::Interpreter::getInvokers() "private";
%javamethodmodifiers uscxml::Interpreter::getIOProcessors() "private";
%javamethodmodifiers uscxml::Data::getCompoundKeys() "private";

%javamethodmodifiers uscxml::Blob::setData(const char* data, size_t length) "private";
%javamethodmodifiers uscxml::Blob::setMimeType(const std::string& mimeType) "private";

%include "../uscxml_beautify.i"


%typemap(javaimports) uscxml::Interpreter %{
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.LinkedList;
import java.net.URL;
%}

%typemap(javacode) uscxml::Interpreter %{
  public static Interpreter fromURI(URL uri) throws org.uscxml.InterpreterException {
    return Interpreter.fromURI(uri.toString());
  }
	
	public Map<String, NativeIOProcessor> getIOProcessors() {
		Map<String, NativeIOProcessor> ioProcs = new HashMap<String, NativeIOProcessor>();
		StringVector keys = getIOProcessorKeys();
		IOProcMap ioProcMap = getIOProcessorsNative();
		for (int i = 0; i < keys.size(); i++) {
			ioProcs.put(keys.get(i), ioProcMap.get(keys.get(i)));
		}
		return ioProcs;
	}

	public Map<String, NativeInvoker> getInvokers() {
		Map<String, NativeInvoker> invokers = new HashMap<String, NativeInvoker>();
		StringVector keys = getInvokerKeys();
		InvokerMap invokerMap = getInvokersNative();
		for (int i = 0; i < keys.size(); i++) {
			invokers.put(keys.get(i), invokerMap.get(keys.get(i)));
		}
		return invokers;
	}
	
	@Override
	public boolean equals(Object other) {
		if (other instanceof Interpreter) {
			return equals((Interpreter)other);
		}
		return hashCode() == other.hashCode();
	}
%}

%rename(getCompoundNative) uscxml::Data::getCompound();
%rename(getArrayNative) uscxml::Data::getArray();
%rename(setCompoundNative) uscxml::Data::setCompound(const std::map<std::string, Data>&);
%rename(setArrayNative) uscxml::Data::setArray(const std::list<Data>&);
%javamethodmodifiers uscxml::Data::getCompound() "private";
%javamethodmodifiers uscxml::Data::getArray() "private";
%javamethodmodifiers uscxml::Data::setCompound(const std::map<std::string, Data>&) "private";
%javamethodmodifiers uscxml::Data::setArray(const std::list<Data>&) "private";
%javamethodmodifiers uscxml::Data::getCompoundKeys() "private";

%typemap(javaimports) uscxml::Data %{
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.LinkedList;
%}

%typemap(javacode) uscxml::Data %{
	public Data(byte[] data, String mimeType) {
		this(uscxmlNativeJavaJNI.new_Data__SWIG_0(), true);
		setBinary(new Blob(data, mimeType));
	}
	
	public Data(Map<String, Data> compound) {
		this(uscxmlNativeJavaJNI.new_Data__SWIG_0(), true);
		setCompound(compound);
	}

	public Data(List<Data> array) {
		this(uscxmlNativeJavaJNI.new_Data__SWIG_0(), true);
		setArray(array);
	}
	
	public Map<String, Data> getCompound() {
		Map<String, Data> compound = new HashMap<String, Data>();
		DataMap dataMap = getCompoundNative();
		StringVector dataMapKeys = getCompoundKeys();
		for (int i = 0; i < dataMapKeys.size(); i++) {
			compound.put(dataMapKeys.get(i), dataMap.get(dataMapKeys.get(i)));
		}
		return compound;
	}
	
	public void setCompound(Map<String, Data> compound) {
		DataMap dataMap = new DataMap();
		for (String key : compound.keySet()) {
			dataMap.set(key, compound.get(key));
		}
		setCompoundNative(dataMap);
	}
	
	public List<Data> getArray() {
		List<Data> array = new LinkedList<Data>();
		DataList dataList = getArrayNative();
		for (int i = 0; i < dataList.size(); i++) {
			array.add(dataList.get(i));
		}
		return array;		
	}
	
	public void setArray(List<Data> array) {
		DataList dataList = new DataList();
		for (Data data : array) {
			dataList.add(data);
		}
		setArrayNative(dataList);
	}
		
%}

%rename(getNameListNative) uscxml::Event::getNameList();
%rename(getParamstNative) uscxml::Event::getParams();
%rename(setNameListNative) uscxml::Event::setNameList(const std::map<std::string, Data>&);
%rename(setParamsNative) uscxml::Event::setParams(const std::multimap<std::string, Data>&);
%javamethodmodifiers uscxml::Event::getNameList() "private";
%javamethodmodifiers uscxml::Event::getNameListKeys() "private";
%javamethodmodifiers uscxml::Event::getParams() "private";
%javamethodmodifiers uscxml::Event::setNameList(const std::map<std::string, Data>&) "private";
%javamethodmodifiers uscxml::Event::setParams(const std::multimap<std::string, Data>&) "private";

%typemap(javaimports) uscxml::Event %{
import java.util.Map;
import java.util.HashMap;
import java.util.List;
import java.util.LinkedList;
%}

%typemap(javacode) uscxml::Event %{
	public Map<String, List<Data>> getParams() {
		Map<String, List<Data>> params = new HashMap<String, List<Data>>();
		ParamMap paramMap = getParamMap();
		StringVector paramMapKeys = getParamMapKeys();
	
		for (int i = 0; i < paramMapKeys.size(); i++) {
			String key = paramMapKeys.get(i);
			DataList dataList = paramMap.get(key);
		
			for (int j = 0; j < dataList.size(); j++) {
				Data data = dataList.get(j);
				if (!params.containsKey(key))
					params.put(key, new LinkedList<Data>());
				params.get(key).add(data);
			}
		}
		return params;
	}
	
	public void setParams(Map<String, List<Data>> params) {
		ParamMap paramMap = new ParamMap();
		for (String key : params.keySet()) {
			DataList datalist = new DataList();
			for (Data data : params.get(key)) {
				datalist.add(data);
			}
			paramMap.set(key, datalist);
		}
		setParamMap(paramMap);
	}
	
	public Map<String, Data> getNameList() {
		Map<String, Data> namelist = new HashMap<String, Data>();
		StringVector nameMapKeys = getNameListKeys();
		DataMap nameMap = getNameListNative();
		
		for (int i = 0; i < nameMapKeys.size(); i++) {
			namelist.put(nameMapKeys.get(i), nameMap.get(nameMapKeys.get(i)));
		}
		return namelist;
	}

	public void setNameList(Map<String, Data> namelist) {
		DataMap nameListMap = new DataMap();
		for (String key : namelist.keySet()) {
			nameListMap.set(key, namelist.get(key));
		}
		setNameListNative(nameListMap);
	}
%}


//***********************************************
// Parse the header file to generate wrappers
//***********************************************

%include "../../../uscxml/Common.h"
%include "../../../uscxml/Factory.h"
%include "../../../uscxml/Message.h"
%include "../../../uscxml/Interpreter.h"
%include "../../../uscxml/concurrency/BlockingQueue.h"
%include "../../../uscxml/server/HTTPServer.h"
%include "../../../uscxml/debug/DebuggerServlet.h"

%include "../../../uscxml/messages/Blob.h"
%include "../../../uscxml/messages/Data.h"
%include "../../../uscxml/messages/Event.h"
%include "../../../uscxml/messages/InvokeRequest.h"
%include "../../../uscxml/messages/SendRequest.h"

%include "../../../uscxml/plugins/DataModel.h"
%include "../../../uscxml/plugins/EventHandler.h"
%include "../../../uscxml/plugins/ExecutableContent.h"
%include "../../../uscxml/plugins/Invoker.h"
%include "../../../uscxml/plugins/IOProcessor.h"

%include "../wrapped/WrappedInvoker.h"
%include "../wrapped/WrappedDataModel.h"
%include "../wrapped/WrappedExecutableContent.h"
%include "../wrapped/WrappedIOProcessor.h"
%include "../wrapped/WrappedInterpreterMonitor.h"


%template(DataList) std::list<uscxml::Data>;
%template(DataMap) std::map<std::string, uscxml::Data>;
%template(StringSet) std::set<std::string>;
%template(StringVector) std::vector<std::string>;
%template(StringList) std::list<std::string>;
%template(ParamMap) std::map<std::string, std::list<uscxml::Data> >;
%template(IOProcMap) std::map<std::string, IOProcessor>;
%template(InvokerMap) std::map<std::string, Invoker>;
%template(ParentQueue) uscxml::concurrency::BlockingQueue<uscxml::SendRequest>;
