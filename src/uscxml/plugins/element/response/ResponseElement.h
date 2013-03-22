#ifndef RESPONSEELEMENT_H_I11KQ39Q
#define RESPONSEELEMENT_H_I11KQ39Q

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class ResponseElement : public ExecutableContentImpl {
public:
	ResponseElement() {}
	virtual ~ResponseElement() {}
	boost::shared_ptr<ExecutableContentImpl> create(Interpreter* interpreter);

	std::string getLocalName() {
		return "response";
	}

	std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}

	bool processChildren() {
		return false;
	}

	void enterElement(const Arabica::DOM::Node<std::string>& node);
	void exitElement(const Arabica::DOM::Node<std::string>& node);

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(ResponseElement, ExecutableContentImpl);
#endif

}


#endif /* end of include guard: RESPONSEELEMENT_H_I11KQ39Q */
