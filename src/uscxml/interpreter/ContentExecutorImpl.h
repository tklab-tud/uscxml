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


#ifndef CONTENTEXECUTORIMPL_H_13F2884F
#define CONTENTEXECUTORIMPL_H_13F2884F

#include "uscxml/Common.h"
#include "uscxml/util/DOM.h"
#include "uscxml/messages/Data.h"
#include "uscxml/messages/Event.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include <xercesc/dom/DOM.hpp>
#include <string>

namespace uscxml {

class USCXML_API ContentExecutorCallbacks {
public:
	virtual void enqueueInternal(const Event& event) = 0;
	virtual void enqueueExternal(const Event& event) = 0;
	virtual void enqueueExternalDelayed(const Event& event, size_t delayMs, const std::string& eventUUID) = 0;
	virtual void cancelDelayed(const std::string& eventId) = 0;

	virtual bool isTrue(const std::string& expr) = 0;
	virtual size_t getLength(const std::string& expr) = 0;

	virtual void setForeach(const std::string& item,
	                        const std::string& array,
	                        const std::string& index,
	                        uint32_t iteration) = 0;

	virtual Data evalAsData(const std::string& expr) = 0;
	virtual Data getAsData(const std::string& expr) = 0;
	virtual void assign(const std::string& location, const Data& data) = 0;


	virtual std::string getInvokeId() = 0;
	virtual std::string getBaseURL() = 0;
	virtual bool checkValidSendType(const std::string& type, const std::string& target) = 0;
	virtual void enqueue(const std::string& type, const std::string& target, size_t delayMs, const Event& sendEvent) = 0;
	virtual void invoke(const std::string& type, const std::string& src, bool autoForward, xercesc::DOMElement* finalize, const Event& invokeEvent) = 0;
	virtual void uninvoke(const std::string& invokeId) = 0;

	virtual const Event& getCurrentEvent() = 0;

	/** Monitoring */
	virtual InterpreterMonitor* getMonitor() = 0;

};

class USCXML_API ContentExecutorImpl {
public:
	ContentExecutorImpl(ContentExecutorCallbacks* callbacks) : _callbacks(callbacks) {}

	virtual void process(xercesc::DOMElement* block, const X& xmlPrefix) = 0;

	virtual void invoke(xercesc::DOMElement* invoke) = 0;
	virtual void uninvoke(xercesc::DOMElement* invoke) = 0;

	virtual void raiseDoneEvent(xercesc::DOMElement* state, xercesc::DOMElement* doneData) = 0;
	virtual Data elementAsData(xercesc::DOMElement* element) = 0;

protected:
	ContentExecutorCallbacks* _callbacks;

};

class USCXML_API BasicContentExecutorImpl : public ContentExecutorImpl {
public:
	BasicContentExecutorImpl(ContentExecutorCallbacks* callbacks) : ContentExecutorImpl(callbacks) {}
	virtual ~BasicContentExecutorImpl() {}

	void processRaise(xercesc::DOMElement* content);
	void processSend(xercesc::DOMElement* element);
	void processCancel(xercesc::DOMElement* content);
	void processIf(xercesc::DOMElement* content);
	void processAssign(xercesc::DOMElement* content);
	void processForeach(xercesc::DOMElement* content);
	void processLog(xercesc::DOMElement* content);
	void processScript(xercesc::DOMElement* content);

	virtual void process(xercesc::DOMElement* block, const X& xmlPrefix);

	virtual void invoke(xercesc::DOMElement* invoke);
	virtual void uninvoke(xercesc::DOMElement* invoke);
	virtual void raiseDoneEvent(xercesc::DOMElement* state, xercesc::DOMElement* doneData);

	virtual Data elementAsData(xercesc::DOMElement* element);

protected:
	void processNameLists(std::map<std::string, Data>& nameMap, xercesc::DOMElement* element);
	void processParams(std::multimap<std::string, Data>& paramMap, xercesc::DOMElement* element);

};

class USCXML_API ContentExecutor {
public:
	PIMPL_OPERATORS(ContentExecutor)

	virtual void process(xercesc::DOMElement* block, const X& xmlPrefix) {
		_impl->process(block, xmlPrefix);
	}

	virtual void invoke(xercesc::DOMElement* invoke) {
		_impl->invoke(invoke);
	}

	virtual void uninvoke(xercesc::DOMElement* invoke) {
		_impl->uninvoke(invoke);
	}

	virtual Data elementAsData(xercesc::DOMElement* element) {
		return _impl->elementAsData(element);
	}

	virtual void raiseDoneEvent(xercesc::DOMElement* state, xercesc::DOMElement* doneData) {
		return _impl->raiseDoneEvent(state, doneData);
	}

protected:
	std::shared_ptr<ContentExecutorImpl> _impl;
};

}

#endif /* end of include guard: CONTENTEXECUTORIMPL_H_13F2884F */
