%module(directors="1") uscxmlNativeLua

// provide a macro for the header files
#define SWIGIMPORTED 1

// fixing a bug for old swig versions with lua wchar:
// https://github.com/swig/swig/commit/c7ef5935496a04f3a83c70af6f841abf3ad7606e
%{
#define wchar wchar_t
%}

%include <stl.i>
%include <std_map.i>
%include <std_string.i>
%include <inttypes.i>
%include "../stl_set.i"
%include "../stl_list.i"

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

// disable warning related to unknown base class
#pragma SWIG nowarn=401
// do not warn when we override symbols via extend
#pragma SWIG nowarn=302
// do not warn when ignoring overrided method
#pragma SWIG nowarn=516

%rename(equals) operator==; // signature is wrong, still useful
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

%include "../uscxml_ignores.i"

// bytearray for Blob::data
// see: http://stackoverflow.com/questions/9934059/swig-technique-to-wrap-unsigned-binary-data

#if 0
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
#endif

//***********************************************
// Beautify important classes
//***********************************************


%include "../uscxml_beautify.i"


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
