#ifndef MMIEVENTS_H_QHO6VT3M
#define MMIEVENTS_H_QHO6VT3M

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#define ELEMENT_CREATOR(elementName) \
boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter) { \
	boost::shared_ptr<elementName> element = boost::shared_ptr<elementName>(new elementName()); \
	element->_interpreter = interpreter; \
	return element; \
}

#define ELEMENT_MMI_CLASS(elementName) \
class elementName##Element : public ExecutableContentImpl { \
public:\
	elementName##Element () {}\
	virtual ~elementName##Element () {}\
	ELEMENT_CREATOR(elementName##Element);\
	std::string getLocalName() { return "elementName"; }\
	std::string getNamespace() { return "http://www.w3.org/2008/04/mmi-arch"; }\
	bool processChildren()     { return false; }\
	void enterElement(const Arabica::DOM::Node<std::string>& node);\
	void exitElement(const Arabica::DOM::Node<std::string>& node) {}\
};

namespace uscxml {

ELEMENT_MMI_CLASS(PrepareRequest);
ELEMENT_MMI_CLASS(StartRequest);
ELEMENT_MMI_CLASS(PauseRequest);
ELEMENT_MMI_CLASS(ResumeRequest);
ELEMENT_MMI_CLASS(CancelRequest);
ELEMENT_MMI_CLASS(ClearContextRequest);
ELEMENT_MMI_CLASS(StatusRequest);
ELEMENT_MMI_CLASS(NewContextResponse);
ELEMENT_MMI_CLASS(PrepareResponse);
ELEMENT_MMI_CLASS(StartResponse);
ELEMENT_MMI_CLASS(PauseResponse);
ELEMENT_MMI_CLASS(ResumeResponse);
ELEMENT_MMI_CLASS(CancelResponse);
ELEMENT_MMI_CLASS(ClearContextResponse);
ELEMENT_MMI_CLASS(StatusResponse);
ELEMENT_MMI_CLASS(DoneNotification);
ELEMENT_MMI_CLASS(NewContextRequest);
ELEMENT_MMI_CLASS(ExtensionNotification);
	
#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FetchElement, ExecutableContentImpl);
#endif

}


#endif /* end of include guard: MMIEVENTS_H_QHO6VT3M */
