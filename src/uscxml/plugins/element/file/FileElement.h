#ifndef FILEELEMENT_H_VJ3JIMEJ
#define FILEELEMENT_H_VJ3JIMEJ

#include <uscxml/Interpreter.h>
#include <sys/stat.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class FileElement : public ExecutableContentImpl {
public:
	enum Operation {
		READ,
		WRITE,
		APPEND
	};

	enum Type {
		XML,
		JSON,
		TEXT,
		BINARY
	};

	FileElement() {
		_sandBoxed = true;
	}
	virtual ~FileElement();
	boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter);

	std::string getLocalName() {
		return "file";
	}

	std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}

	bool processChildren() {
		return false;
	}

	void enterElement(const Arabica::DOM::Node<std::string>& node);
	void exitElement(const Arabica::DOM::Node<std::string>& node);

protected:
	
	bool _sandBoxed;
	std::string _givenUrl;
	URL _actualUrl;
	std::string _filename;
	Operation _operation;
	Type _type;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FileElement, ExecutableContentImpl);
#endif

}

#endif /* end of include guard: FILEELEMENT_H_VJ3JIMEJ */
