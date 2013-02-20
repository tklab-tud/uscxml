#ifndef FETCHELEMENT_H_R6GH94FV
#define FETCHELEMENT_H_R6GH94FV

#include <uscxml/Interpreter.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class FetchElement : public ExecutableContentImpl, public URLMonitor {
public:
	FetchElement() {}
	virtual ~FetchElement();
	boost::shared_ptr<ExecutableContentImpl> create(Interpreter* interpreter);

	std::string getLocalName() {
		return "fetch";
	}

	std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}

	bool processChildren() {
		return false;
	}

	void enterElement(const Arabica::DOM::Node<std::string>& node);
	void exitElement(const Arabica::DOM::Node<std::string>& node);
	void downloadCompleted(const URL& url);
	void downloadFailed(const URL& url, int errorCode);

protected:
	URL _targetUrl;
	std::string _target;
	std::string _callback;
	std::string _type;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FetchElement, Element);
#endif

}

#endif /* end of include guard: FETCHELEMENT_H_R6GH94FV */
