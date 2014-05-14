%module(directors="1", allprotected="1") uscxmlNativeJava

// provide a macro for the header files
#define SWIGIMPORTED 1

// import swig typemaps
//%include <arrays_java.i>
//%include <inttypes.i>

%include <stl.i>
%include <std_map.i>
%include "std_string.i"
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
%ignore operator<<;


//**************************************************
// This ends up in the generated wrapper code
//**************************************************

%{

#include "../../../uscxml/Message.h"
#include "../../../uscxml/Factory.h"
#include "../../../uscxml/Interpreter.h"

//#include <DOM/Document.hpp>
//#include <DOM/Node.hpp>
//#include <DOM/Element.hpp>
//#include <DOM/Attr.hpp>
//#include <DOM/Text.hpp>

#include "JavaInvoker.h"
#include "JavaDataModel.h"

using namespace uscxml;
using namespace Arabica::DOM;

#include "JavaInvoker.cpp"
#include "JavaDataModel.cpp"

%}

%ignore uscxml::NumAttr;
%ignore uscxml::SCXMLParser;
%ignore uscxml::InterpreterImpl;

%ignore create();

%ignore uscxml::Interpreter::getDelayQueue();

%ignore uscxml::JavaInvoker::create(InterpreterImpl*);

%ignore uscxml::JavaDataModel::create(InterpreterImpl*);
%ignore uscxml::JavaDataModel::init(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::JavaDataModel::init(const std::string&, const Data&);
%ignore uscxml::JavaDataModel::assign(const Arabica::DOM::Element<std::string>&, const Arabica::DOM::Document<std::string>&, const std::string&);
%ignore uscxml::JavaDataModel::assign(const std::string&, const Data&);
%ignore uscxml::JavaDataModel::eval(const Arabica::DOM::Element<std::string>&, const std::string&);

%ignore uscxml::Event::Event(const Arabica::DOM::Node<std::string>&);
%ignore uscxml::Event::getStrippedDOM;
%ignore uscxml::Event::getFirstDOMElement;
%ignore uscxml::Event::getDOM();
%ignore uscxml::Event::setDOM(const Arabica::DOM::Document<std::string>&);
%ignore uscxml::Event::toDocument();

%template(DataList) std::list<uscxml::Data>;
%template(DataMap) std::map<std::string, uscxml::Data>;
%template(StringSet) std::set<std::string>;
%template(StringVector) std::vector<std::string>;
%template(ParamPair) std::pair<std::string, uscxml::Data>;
%template(ParamPairVector) std::vector<std::pair<std::string, uscxml::Data> >;
%template(IOProcMap) std::map<std::string, uscxml::IOProcessor>;

%rename Data DataNative;
# %typemap(jstype) uscxml::Data "Data"
# %typemap(javaout) uscxml::Data {
# 	return new Data(new DataNative($jnicall, $owner));
# }

# %typemap(javadirectorin) uscxml::Data "new Data($jniinput)"
# %typemap(javadirectorout) uscxml::Data "new Data($jniinput)"

%feature("director") uscxml::JavaInvoker;
%feature("director") uscxml::JavaDataModel;

// translate param multimap to Map<String, List<Data> >
%rename(getParamsNative) uscxml::Event::getParams();
%javamethodmodifiers uscxml::Event::getParams() "private";

%extend uscxml::Event {
	std::vector<std::pair<std::string, Data> > getParamPairs() {
		std::vector<std::pair<std::string, Data> > pairs;
    std::multimap<std::string, Data>::iterator paramPairIter = self->getParams().begin();
		while(paramPairIter != self->getParams().end()) {
			pairs.push_back(*paramPairIter);
			paramPairIter++;
		}
		return pairs;
	}
};

%extend uscxml::Interpreter {
	std::vector<std::string> getIOProcessorKeys() {
		std::vector<std::string> keys;
    std::map<std::string, IOProcessor>::const_iterator iter = self->getIOProcessors().begin();
		while(iter != self->getIOProcessors().end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}
};

%extend uscxml::Data {
	std::vector<std::string> getCompundKeys() {
		std::vector<std::string> keys;
    std::map<std::string, Data>::const_iterator iter = self->compound.begin();
		while(iter != self->compound.end()) {
			keys.push_back(iter->first);
			iter++;
		}
		return keys;
	}
};



//***********************************************
// Parse the header file to generate wrappers
//***********************************************

%include "../../../uscxml/Common.h"
%include "../../../uscxml/Factory.h"
%include "../../../uscxml/Message.h"
%include "../../../uscxml/Interpreter.h"
#include "../../../uscxml/DOMUtils.h"

# %include <DOM/Document.hpp>
# %include <DOM/Node.hpp>
# %include <DOM/Element.hpp>
# %include <DOM/Attr.hpp>
# %include <DOM/Text.hpp>

%include "JavaInvoker.h"
%include "JavaDataModel.h"

# %template(XMLDocument) Arabica::DOM::Document<std::string>;
# %template(XMLNode) Arabica::DOM::Node<std::string>;
# %template(XMLElement) Arabica::DOM::Element<std::string>;
# %template(XMLAttr) Arabica::DOM::Attr<std::string>;
# %template(XMLText) Arabica::DOM::Text<std::string>; 
