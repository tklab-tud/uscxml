/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#ifndef INTERPRETER_H_6CD5A168
#define INTERPRETER_H_6CD5A168

#include <map>
#include <mutex>
#include <string>

#include "Common.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/InterpreterMonitor.h" // beware cyclic reference!
#include "uscxml/debug/InterpreterIssue.h" // beware cyclic reference!
#include <xercesc/dom/DOM.hpp>

namespace uscxml {

class InterpreterMonitor; // forward declare

class USCXML_API InterpreterOptions {
public:
	InterpreterOptions() :
		verbose(false),
		validate(false),
		withHTTP(true),
		withHTTPS(true),
		withWS(true),
		logLevel(0),
		httpPort(5080),
		httpsPort(5443),
		wsPort(5081) {
	}

	bool verbose;
	bool validate;
	bool withHTTP;
	bool withHTTPS;
	bool withWS;
	int logLevel;
	unsigned short httpPort;
	unsigned short httpsPort;
	unsigned short wsPort;
	std::string pluginPath;
	std::string certificate;
	std::string privateKey;
	std::string publicKey;
	std::vector<std::pair<std::string, InterpreterOptions*> > interpreters;
	std::map<std::string, std::string> additionalParameters;

	std::string error;

	operator bool() {
		return error.length() == 0;
	}

	static void printUsageAndExit(const char* progName);
	static InterpreterOptions fromCmdLine(int argc, char** argv);

};

class USCXML_API Interpreter {
public:
	static Interpreter fromDocument(xercesc::DOMDocument* dom,
	                                const std::string& baseURL,
	                                bool copy = true);
	static Interpreter fromElement(xercesc::DOMElement* element,
	                               const std::string& baseURL);
	static Interpreter fromXML(const std::string& xml,
	                           const std::string& baseURL);
	static Interpreter fromURL(const std::string& URL);
	static Interpreter fromClone(const Interpreter& other);

	PIMPL_OPERATORS(Interpreter);

	void reset() {
		return _impl->reset();
	}

	InterpreterState step(bool blocking = false) {
		return _impl->step(blocking);
	};

	void cancel() {
		return _impl->cancel();
	}

	virtual bool isInState(const std::string& stateId) {
		return _impl->isInState(stateId);
	}

	InterpreterState getState() {
		return _impl->getState();
	}

	std::list<xercesc::DOMElement*> getConfiguration() {
		return _impl->getConfiguration();
	}

	virtual void receive(const Event& event) {
		_impl->enqueueExternal(event);
	}

	void setActionLanguage(ActionLanguage actionLanguage) {
		return _impl->setActionLanguage(actionLanguage);
	}

	void setMonitor(InterpreterMonitor* monitor) {
		return _impl->setMonitor(monitor);
	}

	std::list<InterpreterIssue> validate() {
		return InterpreterIssue::forInterpreter(_impl.get());
	}

	std::shared_ptr<InterpreterImpl> getImpl() const {
		return _impl;
	}

protected:
	std::shared_ptr<InterpreterImpl> _impl;

};

class USCXML_API StateTransitionMonitor : public uscxml::InterpreterMonitor {
public:
	StateTransitionMonitor(Interpreter interpreter) : _interpreter(interpreter) {}
	virtual ~StateTransitionMonitor() {}

	virtual void beforeTakingTransition(const xercesc::DOMElement* transition);
	virtual void beforeExecutingContent(const xercesc::DOMElement* element);
	virtual void onStableConfiguration();
	virtual void beforeProcessingEvent(const uscxml::Event& event);
	virtual void beforeExitingState(const xercesc::DOMElement* state);
	virtual void beforeEnteringState(const xercesc::DOMElement* state);
	virtual void beforeMicroStep();

protected:
	Interpreter _interpreter;
	static std::recursive_mutex _mutex;
};

}

#endif /* end of include guard: INTERPRETER_H_6CD5A168 */
