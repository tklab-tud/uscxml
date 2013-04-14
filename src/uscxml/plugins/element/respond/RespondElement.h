#ifndef RESPONDELEMENT_H_I11KQ39Q
#define RESPONDELEMENT_H_I11KQ39Q

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class RespondElement : public ExecutableContentImpl {
public:
	RespondElement() {}
	virtual ~RespondElement() {}
	boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter);

	std::string getLocalName() {
		return "respond";
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
PLUMA_INHERIT_PROVIDER(RespondElement, ExecutableContentImpl);
#endif

}


#endif /* end of include guard: RESPONDELEMENT_H_I11KQ39Q */
