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

#ifndef CONTENTEXECUTORIMPL_H_3ABA8969
#define CONTENTEXECUTORIMPL_H_3ABA8969


#include "uscxml/Common.h"
#include "uscxml/messages/Event.h"
#include "uscxml/interpreter/InterpreterMonitor.h"
#include "uscxml/interpreter/Logging.h"

#include <string>
#include <set>

namespace XERCESC_NS {
class DOMDocument;
class DOMNode;
}

namespace uscxml {

class X;

/**
 * @ingroup execcontent
 * @ingroup callback
 */
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
	virtual void invoke(const std::string& type, const std::string& src, bool autoForward, XERCESC_NS::DOMElement* finalize, const Event& invokeEvent) = 0;
	virtual void uninvoke(const std::string& invokeId) = 0;

	virtual const Event& getCurrentEvent() = 0;

	/** Monitoring */
	virtual std::set<InterpreterMonitor*> getMonitors() = 0;
	virtual Interpreter getInterpreter() = 0;
	virtual Logger getLogger() = 0;

};

/**
 * @ingroup execcontent
 * @ingroup impl
 */
class USCXML_API ContentExecutorImpl {
public:
	ContentExecutorImpl(ContentExecutorCallbacks* callbacks) : _callbacks(callbacks) {}

	virtual std::shared_ptr<ContentExecutorImpl> create(ContentExecutorCallbacks* callbacks) = 0;

	virtual void process(XERCESC_NS::DOMElement* block, const X& xmlPrefix) = 0;

	virtual void invoke(XERCESC_NS::DOMElement* invoke) = 0;
	virtual void uninvoke(XERCESC_NS::DOMElement* invoke) = 0;

	virtual void raiseDoneEvent(XERCESC_NS::DOMElement* state, XERCESC_NS::DOMElement* doneData) = 0;
	virtual Data elementAsData(XERCESC_NS::DOMElement* element) = 0;

protected:
	ContentExecutorCallbacks* _callbacks;

};

}

#endif /* end of include guard: CONTENTEXECUTORIMPL_H_3ABA8969 */
