%module(directors="1", allprotected="1") uscxmlNativeJava

// import swig typemaps
//%include <arrays_java.i>
//%include <inttypes.i>

%include <stl.i>
%include <std_map.i>
%include <inttypes.i>
%include "stl_set.i"
%include "stl_list.i"

%include <boost_shared_ptr.i>


typedef uscxml::Data Data;
typedef uscxml::Event Event;
typedef uscxml::InvokeRequest InvokeRequest;
typedef uscxml::SendRequest SendRequest;

// disable warning related to unknown base class
#pragma SWIG nowarn=401
//%ignore boost::enable_shared_from_this;

%javaconst(1);

# %shared_ptr(uscxml::dom::Element);
# %shared_ptr(uscxml::dom::Executable);

%rename(equals) operator==; 
%rename(isValid) operator bool;
%ignore operator!=;
%ignore operator<;
%ignore operator=;
%ignore operator[];
%ignore operator std::list<Data>;
%ignore operator std::string;
%ignore operator std::map<std::string,Data>;


//**************************************************
// This ends up in the generated wrapper code
//**************************************************

%{

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"
#include "JavaInvoker.h"
#include "JavaDataModel.h"

using namespace uscxml;

#include "JavaInvoker.cpp"
#include "JavaDataModel.cpp"

%}

%rename(toString) operator<<;

%ignore uscxml::NumAttr;
%ignore uscxml::SCXMLParser;
%ignore uscxml::InterpreterImpl;

%ignore uscxml::Interpreter::getDelayQueue();

%ignore uscxml::JavaInvoker::create(InterpreterImpl*);
%ignore uscxml::JavaDataModel::create(InterpreterImpl*);

%template(DataMap) std::map<std::string, uscxml::Data>;
%template(DataList) std::list<uscxml::Data>;
%template(StringSet) std::set<std::string>;


%feature("director") uscxml::JavaInvoker;
%feature("director") uscxml::JavaDataModel;

//***********************************************
// Parse the header file to generate wrappers
//***********************************************

#define SWIGIMPORTED 1
%include "../../../uscxml/Factory.h"
%include "../../../uscxml/Message.h"
%include "../../../uscxml/Interpreter.h"
%include "JavaInvoker.h"
%include "JavaDataModel.h"

