%module(directors="1", allprotected="1") uscxmlNativeCSharp

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
typedef uscxml::Invoker Invoker;
typedef uscxml::IOProcessor IOProcessor;
typedef uscxml::DataModel DataModel;
typedef uscxml::DataModelExtension DataModelExtension;
typedef uscxml::ExecutableContent ExecutableContent;
typedef uscxml::InvokerImpl InvokerImpl;
typedef uscxml::IOProcessorImpl IOProcessorImpl;
typedef uscxml::DataModelImpl DataModelImpl;
typedef uscxml::ExecutableContentImpl ExecutableContentImpl;
typedef uscxml::InterpreterIssue InterpreterIssue;

%feature("director") uscxml::WrappedInvoker;
%feature("director") uscxml::WrappedDataModel;
%feature("director") uscxml::WrappedDataModelExtension;
%feature("director") uscxml::WrappedIOProcessor;
%feature("director") uscxml::WrappedExecutableContent;
%feature("director") uscxml::WrappedInterpreterMonitor;

// disable warnings 

// unknown base class
#pragma SWIG nowarn=401
// override symbols via extend
#pragma SWIG nowarn=302
// ignoring overrided method
#pragma SWIG nowarn=516
// pointer from director
#pragma SWIG nowarn=473
// renamed params -> _params
#pragma SWIG nowarn=314

%csconst(1);

%rename(equals) operator==; 
%rename(isValid) operator bool;


//**************************************************
// This ends up in the generated wrapper code
//**************************************************

%{

#include "uscxml/config.h"
#include "../../../uscxml/Interpreter.h"
#include "../../../uscxml/debug/InterpreterIssue.h"
#include "../../../uscxml/interpreter/InterpreterState.h"
#include "../../../uscxml/interpreter/InterpreterMonitor.h"

#include "../../../uscxml/messages/Data.h"
#include "../../../uscxml/messages/Event.h"
#include "../../../uscxml/util/DOM.h"

#include "../../../uscxml/plugins/Factory.h"
#include "../../../uscxml/plugins/DataModelImpl.h"

#include "../wrapped/WrappedInvoker.h"
#include "../wrapped/WrappedDataModel.h"
#include "../wrapped/WrappedActionLanguage.h"
#include "../wrapped/WrappedExecutableContent.h"
#include "../wrapped/WrappedIOProcessor.h"
#include "../wrapped/WrappedInterpreterMonitor.h"

using namespace uscxml;
using namespace XERCESC_NS;

// the wrapped* C++ classes get rid of DOM nodes and provide more easily wrapped base classes
#include "../wrapped/WrappedInvoker.cpp"
#include "../wrapped/WrappedDataModel.cpp"
#include "../wrapped/WrappedActionLanguage.cpp"
#include "../wrapped/WrappedExecutableContent.cpp"
#include "../wrapped/WrappedIOProcessor.cpp"
#include "../wrapped/WrappedInterpreterMonitor.cpp"

%}

// see http://binf.gmu.edu/software/SWIG/CSharp.html#csharp_exceptions
%insert(runtime) %{
  // Code to handle throwing of C# CustomApplicationException from C/C++ code.
  // The equivalent delegate to the callback, CSharpExceptionCallback_t, is CustomExceptionDelegate
  // and the equivalent customExceptionCallback instance is customDelegate
  typedef void (SWIGSTDCALL* CSharpExceptionCallback_t)(const char *);
  CSharpExceptionCallback_t customExceptionCallback = NULL;

  extern "C" SWIGEXPORT
  void SWIGSTDCALL CustomExceptionRegisterCallback(CSharpExceptionCallback_t customCallback) {
    customExceptionCallback = customCallback;
  }

  // Note that SWIG detects any method calls named starting with
  // SWIG_CSharpSetPendingException for warning 845
  static void SWIG_CSharpSetPendingExceptionCustom(const char *msg) {
    customExceptionCallback(msg);
  }
%}

%pragma(csharp) imclasscode=%{
  class CustomExceptionHelper {
    // C# delegate for the C/C++ customExceptionCallback
    public delegate void CustomExceptionDelegate(string message);
    static CustomExceptionDelegate customDelegate =
                                   new CustomExceptionDelegate(SetPendingCustomException);

    [System.Runtime.InteropServices.DllImport("$dllimport", EntryPoint="CustomExceptionRegisterCallback")]
    public static extern
           void CustomExceptionRegisterCallback(CustomExceptionDelegate customCallback);

    static void SetPendingCustomException(string message) {
      SWIGPendingException.Set(new org.uscxml.InterpreterException(message));
    }

    static CustomExceptionHelper() {
      CustomExceptionRegisterCallback(customDelegate);
    }
  }
  static CustomExceptionHelper exceptionHelper = new CustomExceptionHelper();
%}


%define WRAP_THROW_EXCEPTION( MATCH )
%exception MATCH %{
try {
  $action
} catch (uscxml::Event& e) {
  std::stringstream ss;
  ss << std::endl << e;
  SWIG_CSharpSetPendingExceptionCustom(ss.str().c_str());
}
%}
%enddef

WRAP_THROW_EXCEPTION(uscxml::Interpreter::fromXML);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::fromURI);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::step);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::interpret);


%define WRAP_TO_STRING( CLASSNAME )
%csmethodmodifiers CLASSNAME::ToString() "public override";
%extend CLASSNAME {	
	virtual std::string ToString() {
		std::stringstream ss;
		ss << *self;
		return ss.str();
	}
};
%enddef

WRAP_TO_STRING(uscxml::Event);
WRAP_TO_STRING(uscxml::Data);
WRAP_TO_STRING(uscxml::InterpreterIssue);

%include "../uscxml_ignores.i"

// InterpreterMonitor -> StateTransitionMonitor
%ignore uscxml::StateTransitionMonitor;

//***********************************************
// Beautify important classes
//***********************************************


// byte[] signature for Blob get/setData
// see http://permalink.gmane.org/gmane.comp.programming.swig/5804

%csmethodmodifiers uscxml::Blob::setData(const char* data, size_t length) "private";
%csmethodmodifiers uscxml::Blob::setMimeType(const std::string& mimeType) "private";
%csmethodmodifiers uscxml::Blob::Blob(const char* data, size_t size, const std::string& mimeType) "private";
%csmethodmodifiers uscxml::Blob::Blob(const char* data, size_t size) "private";

%typemap(cscode) uscxml::Blob %{
  public Blob(byte[] data, string mimeType) : this(uscxmlNativeCSharpPINVOKE.new_Blob__SWIG_2(data, (uint)data.Length, mimeType), true) {
    if (uscxmlNativeCSharpPINVOKE.SWIGPendingException.Pending) throw uscxmlNativeCSharpPINVOKE.SWIGPendingException.Retrieve();
  }
	
%}

%typemap(imtype, out="System.IntPtr") const char *data "byte[]"
%typemap(cstype) const char *data "byte[]"
%typemap(in) const char *data %{ $1 = ($1_ltype)$input; %}
%typemap(csin) const char *data "$csinput"

%typemap(imtype, out="System.IntPtr") char* getData "byte[]"
%typemap(cstype) char* getData "byte[]"

%typemap(csout) char* getData %{
	{
    byte[] ret = new byte[this.getSize()];
    System.IntPtr data = $imcall;
    System.Runtime.InteropServices.Marshal.Copy(data, ret, 0, (int)this.getSize());
    return ret;
  }
%}

// make sure we do not get the default with SWIG_csharp_string_callback
%typemap(out) char* getData {
  $result = (char *)result;
}



%csmethodmodifiers uscxml::Event::getParamMap() "private";
%csmethodmodifiers uscxml::Event::getParamMapKeys() "private";
%csmethodmodifiers uscxml::Event::setParamMap(const std::map<std::string, std::list<uscxml::Data> >&) "private";
%csmethodmodifiers uscxml::Event::getNameListKeys() "private";
%csmethodmodifiers uscxml::Interpreter::getIOProcessorKeys() "private";
%csmethodmodifiers uscxml::Interpreter::getInvokerKeys() "private";
%csmethodmodifiers uscxml::Interpreter::getInvokers() "private";
%csmethodmodifiers uscxml::Interpreter::getIOProcessors() "private";
%csmethodmodifiers uscxml::Data::getCompoundKeys() "private";

%include "../uscxml_beautify.i"

%typemap(csimports) uscxml::Interpreter %{
using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
%}

%typemap(cscode) uscxml::Interpreter %{
	public Dictionary<string, NativeIOProcessor> getIOProcessors() {
		Dictionary<string, NativeIOProcessor> ioProcs = new Dictionary<string, NativeIOProcessor>();
		StringVector keys = getIOProcessorKeys();
		IOProcMap ioProcMap = getIOProcessorsNative();
		for (size_t i = 0; i < keys.Count; i++) {
			ioProcs[keys[i]] = ioProcMap[keys[i]];
		}
		return ioProcs;
	}
	
	public Dictionary<string, NativeInvoker> getInvokers() {
		Dictionary<string, NativeInvoker> invokers = new Dictionary<string, NativeInvoker>();
		StringVector keys = getInvokerKeys();
		InvokerMap invokerMap = getInvokersNative();
		for (size_t i = 0; i < keys.Count; i++) {
			invokers[keys[i]] = invokerMap[keys[i]];
		}
		return invokers;
	}
	
%}


%rename(getCompoundNative) uscxml::Data::getCompound();
%rename(getArrayNative) uscxml::Data::getArray();
%rename(setCompoundNative) uscxml::Data::setCompound(const std::map<std::string, Data>&);
%rename(setArrayNative) uscxml::Data::setArray(const std::list<Data>&);
%csmethodmodifiers uscxml::Data::getCompound() "private";
%csmethodmodifiers uscxml::Data::getArray() "private";
%csmethodmodifiers uscxml::Data::setCompound(const std::map<std::string, Data>&) "private";
%csmethodmodifiers uscxml::Data::setArray(const std::list<Data>&) "private";
%csmethodmodifiers uscxml::Data::getCompoundKeys() "private";

%typemap(csimports) uscxml::Data %{
using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
%}

%typemap(cscode) uscxml::Data %{
	public Data(byte[] data, String mimeType) : this() {
		setBinary(new Blob(data, mimeType));
	}

	public Data(List<Data> arr) : this() {
		setArray(arr);
	}

	public Data(Dictionary<string, Data> compound) : this() {
		setCompound(compound);
	}

	public Dictionary<string, Data> getCompound() {
		Dictionary<string, Data> compound = new Dictionary<string, Data>();
		DataMap dataMap = getCompoundNative();
		StringVector dataMapKeys = getCompoundKeys();
		for (size_t i = 0; i < dataMapKeys.Count; i++) {
			compound[dataMapKeys[i]] = dataMap[dataMapKeys[i]];
		}
		return compound;
	}

	public void setCompound(Dictionary<string, Data> compound) { 
		DataMap dataMap = new DataMap();
		foreach(KeyValuePair<string, Data> entry in compound) {
			dataMap.Add(entry);
		}
		setCompoundNative(dataMap);
	}

	public List<Data> getArray() {
		List<Data> arr = new List<Data>();
		DataList dataList = getArrayNative();
		for (size_t i = 0; i < dataList.size(); i++) {
			arr.Add(dataList.get(i));
		}
		return arr;
	}

	public void setArray(List<Data> arr) {
		DataList dataList = new DataList();
		foreach (Data data in arr) {
			dataList.add(data);
		}
		setArrayNative(dataList);
	}
		
%}

%rename(getNameListNative) uscxml::Event::getNameList();
%rename(getParamsNative) uscxml::Event::getParams();
%rename(setNameListNative) uscxml::Event::setNameList(const std::map<std::string, Data>&);
%rename(setParamsNative) uscxml::Event::setParams(const std::multimap<std::string, Data>&);
%csmethodmodifiers uscxml::Event::getNameList() "private";
%csmethodmodifiers uscxml::Event::getNameListKeys() "private";
%csmethodmodifiers uscxml::Event::getParams() "private";
%csmethodmodifiers uscxml::Event::setNameList(const std::map<std::string, Data>&) "private";
%csmethodmodifiers uscxml::Event::setParams(const std::multimap<std::string, Data>&) "private";

%typemap(csimports) uscxml::Event %{
	using System;
	using System.Collections.Generic;
	using System.Runtime.InteropServices;
%}

%typemap(cscode) uscxml::Event %{
	public Dictionary<string, List<Data> > getParams() { 
		Dictionary<string, List<Data>> parameters = new Dictionary<string, List<Data>>();
		ParamMap paramMap = getParamMap();

		foreach (KeyValuePair<string, DataList> entry in paramMap) {
			DataList dataList = entry.Value;
			List<Data> paramList = new List<Data>();
			for (size_t i = 0; i < dataList.size(); i++) {
				Data data = dataList.get(i);
				paramList.Add(data);
			}
			parameters.Add(entry.Key, paramList);
		}
		return parameters;
	}

	public void setParams(Dictionary<string, List<Data>> parameters) { 
		ParamMap paramMap = new ParamMap();
		foreach(KeyValuePair<string, List<Data>> entry in parameters) {
			DataList dataList = new DataList();
			foreach (Data data in entry.Value) {
				dataList.add(data);
			}
			paramMap.Add(entry.Key, dataList);
		}
		setParamMap(paramMap);
	}

	public Dictionary<string, Data> getNameList() {
		Dictionary<string, Data> nameList = new Dictionary<string, Data>();
		DataMap nameListMap = getNameListNative();
		StringVector nameListMapKeys = getNameListKeys();
		for (size_t i = 0; i < nameListMapKeys.Count; i++) {
			nameList[nameListMapKeys[i]] = nameListMap[nameListMapKeys[i]];
		}
		return nameList;
	}

	public void setNameList(Dictionary<string, Data> nameList) {
		DataMap dataMap = new DataMap();
		foreach (KeyValuePair<string, Data> entry in nameList) {
			dataMap.Add(entry);
		}
		setNameListNative(dataMap);
	}
%}

//***********************************************
// Parse the header file to generate wrappers
//***********************************************

%include "../../../uscxml/Common.h"
%include "../../../uscxml/messages/Blob.h"
%include "../../../uscxml/messages/Data.h"
%include "../../../uscxml/messages/Event.h"

%include "../../../uscxml/plugins/Factory.h"
%include "../../../uscxml/interpreter/InterpreterState.h"
%include "../../../uscxml/interpreter/InterpreterMonitor.h"

//%include "../../../uscxml/interpreter/MicroStep.h"
//%include "../../../uscxml/interpreter/ContentExecutor.h"

%include "../../../uscxml/Interpreter.h"
%include "../../../uscxml/debug/InterpreterIssue.h"

%include "../../../uscxml/plugins/EventHandler.h"

%include "../../../uscxml/plugins/DataModel.h"
%include "../../../uscxml/plugins/DataModelImpl.h"
%include "../../../uscxml/plugins/ExecutableContent.h"
%include "../../../uscxml/plugins/ExecutableContentImpl.h"
%include "../../../uscxml/plugins/Invoker.h"
%include "../../../uscxml/plugins/InvokerImpl.h"
%include "../../../uscxml/plugins/IOProcessor.h"
%include "../../../uscxml/plugins/IOProcessorImpl.h"

%include "../wrapped/WrappedInvoker.h"
%include "../wrapped/WrappedDataModel.h"
%include "../wrapped/WrappedActionLanguage.h"
%include "../wrapped/WrappedExecutableContent.h"
%include "../wrapped/WrappedIOProcessor.h"
%include "../wrapped/WrappedInterpreterMonitor.h"

%template(IssueList) std::list<uscxml::InterpreterIssue>;
%template(DataList) std::list<uscxml::Data>;
%template(DataMap) std::map<std::string, uscxml::Data>;
%template(StringSet) std::set<std::string>;
%template(StringVector) std::vector<std::string>;
%template(StringList) std::list<std::string>;
%template(ParamMap) std::map<std::string, std::list<uscxml::Data> >;
%template(IOProcMap) std::map<std::string, IOProcessor>;
%template(InvokerMap) std::map<std::string, Invoker>;
