%module(directors="1", allprotected="1") uscxmlNativeJava

// provide a macro for the header files
#define SWIGIMPORTED 1

%include <stl.i>
%include <std_map.i>
%include <std_string.i>
%include <inttypes.i>
%include "../stl_set.i"
%include "../stl_list.i"
%include "enums.swg"

%include <std_shared_ptr.i>

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

%javaconst(1);

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
#include "../../../uscxml/plugins/ExecutableContent.h"

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

// throw from c++ to java
%define WRAP_THROW_EXCEPTION( MATCH )
%javaexception("org.uscxml.InterpreterException") MATCH {
  try {
    $action
  }
  catch ( uscxml::Event& e ) {
    jclass eclass = jenv->FindClass("org/uscxml/InterpreterException");
    if ( eclass ) {
      std::stringstream ss;
      jenv->ThrowNew( eclass, ss.str().c_str() );
    }
  }
}
%enddef

WRAP_THROW_EXCEPTION(uscxml::Interpreter::fromXML);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::fromURL);
WRAP_THROW_EXCEPTION(uscxml::Interpreter::step);

// throw from java directors to c++
%typemap(javabase) uscxml::Event "java.lang.RuntimeException";
%rename(getMessage) uscxml::ErrorEvent::toString;

%define WRAP_THROWS_ERROREVENT( MATCH )
%feature("director:except") MATCH {
  jthrowable swigerror = jenv->ExceptionOccurred();
  if (Swig::ExceptionMatches(jenv, swigerror, "org/uscxml/ErrorEvent")) {
    jenv->ExceptionClear();
		jenv->DeleteLocalRef(swigjobj);
		ERROR_EXECUTION_THROW(Swig::JavaExceptionMessage(jenv, swigerror).message());
  }
}
%enddef
WRAP_THROWS_ERROREVENT(uscxml::WrappedDataModel::getLength);
WRAP_THROWS_ERROREVENT(uscxml::WrappedDataModel::setForeach);


%typemap(directorthrows) uscxml::ErrorEvent %{
  if (Swig::ExceptionMatches(jenv, $error, "$packagepath/$javaclassname"))
    throw $1_type(Swig::JavaExceptionMessage(jenv, $error).message());
%}

%catches(uscxml::ErrorEvent) uscxml::WrappedDataModel::getLength;


// provide a hashcode
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
WRAP_TO_STRING(uscxml::InterpreterIssue);

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
