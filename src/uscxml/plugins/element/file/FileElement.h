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

	void enterElement(const Arabica::DOM::Element<std::string>& node);
	void exitElement(const Arabica::DOM::Element<std::string>& node);

protected:

	bool _sandBoxed;
	std::string _givenUrl;
	URL _actualUrl;
	std::string _filepath;
	Operation _operation;
	Type _type;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(FileElement, ExecutableContentImpl);
#endif

}

#endif /* end of include guard: FILEELEMENT_H_VJ3JIMEJ */
