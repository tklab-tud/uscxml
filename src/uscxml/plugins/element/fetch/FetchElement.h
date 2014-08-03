/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

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
	boost::shared_ptr<ExecutableContentImpl> create(InterpreterImpl* interpreter);

	std::string getLocalName() {
		return "fetch";
	}

	std::string getNamespace() {
		return "http://www.w3.org/2005/07/scxml";
	}

	bool processChildren() {
		return false;
	}

	void enterElement(const Arabica::DOM::Element<std::string>& node);
	void exitElement(const Arabica::DOM::Element<std::string>& node);
	void downloadCompleted(const URL& url);
	void downloadFailed(const URL& url, int errorCode);

protected:
	URL _targetUrl;
	std::string _target;
	std::string _callback;
	std::string _type;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FetchElement, ExecutableContentImpl);
#endif

}

#endif /* end of include guard: FETCHELEMENT_H_R6GH94FV */
