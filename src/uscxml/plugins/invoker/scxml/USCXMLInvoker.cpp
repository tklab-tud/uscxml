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

#include "USCXMLInvoker.h"
#include "uscxml/util/DOM.h"
#include "uscxml/interpreter/LoggingImpl.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#ifdef UNIX
#include <pthread.h>
#endif

namespace uscxml {

// msxml.h should die in a fire for polluting the global namespace
// using namespace XERCESC_NS;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new USCXMLInvokerProvider() );
	return true;
}
#endif

USCXMLInvoker::USCXMLInvoker() {
	_parentQueue = EventQueue(std::shared_ptr<ParentQueueImpl>(new ParentQueueImpl(this)));
	_thread = NULL;
	_isActive = false;
	_isStarted = false;
}


USCXMLInvoker::~USCXMLInvoker() {
	stop();
}

void USCXMLInvoker::start() {
	_isStarted = true;
	_thread = new std::thread(USCXMLInvoker::run, this);
}

void USCXMLInvoker::stop() {
	_isStarted = false;
	_isActive = false;

	if (_thread) {
		/**
		 * We cannot join the invoked thread if it is blocking at an external
		 * receive. Cancel will finalize and unblock.
		 */
		_invokedInterpreter.cancel();
		_thread->join();
		delete _thread;
		_thread = NULL;
	}
}

void USCXMLInvoker::deserialize(const Data& encodedState) {
	_invokedInterpreter.deserialize(encodedState["intepreter"]);
}

Data USCXMLInvoker::serialize() {
	Data encodedState;

	std::lock_guard<std::recursive_mutex> lock(_mutex);

	InterpreterState state = USCXML_UNDEF;
	while((state = _invokedInterpreter.getState())) {
		if (state != USCXML_IDLE && state != USCXML_MACROSTEPPED && state != USCXML_FINISHED) {
			_cond.wait(_mutex);
		} else {
			break;
		}
	}

	encodedState["intepreter"] = Data(_invokedInterpreter.serialize());

	return encodedState;
}

void USCXMLInvoker::uninvoke() {
	_isActive = false;
	stop();
}

void USCXMLInvoker::eventFromSCXML(const Event& event) {
	if (_isActive) {
		_invokedInterpreter.receive(event);
	}
}

void USCXMLInvoker::run(void* instance) {
	USCXMLInvoker* INSTANCE = (USCXMLInvoker*)instance;

#ifdef APPLE
	std::string threadName;
	threadName += "uscxml::";
	threadName += (INSTANCE->_invokedInterpreter.getImpl()->_name.size() > 0 ? INSTANCE->_invokedInterpreter.getImpl()->_name : "anon");
	threadName += ".scxml";

	pthread_setname_np(threadName.c_str());
#endif

	InterpreterState state = USCXML_UNDEF;
	while(state != USCXML_FINISHED) {
		std::lock_guard<std::recursive_mutex> lock(INSTANCE->_mutex);
		state = INSTANCE->_invokedInterpreter.step(200);
		INSTANCE->_cond.notify_all();
	}

	if (INSTANCE->_isActive) {
		// we finished on our own and were not cancelled
		Event e;
		e.eventType = Event::PLATFORM;
		e.invokeid = INSTANCE->_invokedInterpreter.getImpl()->getInvokeId();
		e.name = "done.invoke." + e.invokeid;
		INSTANCE->_callbacks->enqueueExternal(e);
	}

	INSTANCE->_isActive = false;
}

std::shared_ptr<InvokerImpl> USCXMLInvoker::create(InvokerCallbacks* callbacks) {
	std::shared_ptr<USCXMLInvoker> invoker(new USCXMLInvoker());
	invoker->_callbacks = callbacks;
	return invoker;
}

Data USCXMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void USCXMLInvoker::invoke(const std::string& source, const Event& invokeEvent) {
	if (source.length() > 0) {
		_invokedInterpreter = Interpreter::fromURL(source);
	} else if (invokeEvent.data.node) {
		XERCESC_NS::DOMImplementation* implementation = XERCESC_NS::DOMImplementationRegistry::getDOMImplementation(X("core"));
		XERCESC_NS::DOMDocument* document = implementation->createDocument();

		// we need to import the parent - to support xpath test150
		XERCESC_NS::DOMNode* newNode = document->importNode(invokeEvent.data.node, true);
		document->appendChild(newNode);

		// TODO: where do we get the namespace from?
		_invokedInterpreter = Interpreter::fromDocument(document, _callbacks->getBaseURL(), false);
	} else if (invokeEvent.data.atom.size() > 0) {
		// test530 when deserializing
		_invokedInterpreter = Interpreter::fromXML(invokeEvent.data.atom, _callbacks->getBaseURL());

	} else {
		_isActive = false;
		ERROR_PLATFORM_THROW("Cannot invoke nested SCXML interpreter, neither src attribute nor content nor DOM is given");
	}

	if (_invokedInterpreter) {
		_invokedInterpreter.getImpl()->_parentQueue = _parentQueue;
		_invokedInterpreter.getImpl()->_invokeId = invokeEvent.invokeid;

		// test240 assumes that invoke request params will carry over to the datamodel
		_invokedInterpreter.getImpl()->_invokeReq = invokeEvent;

		// create new instances from the parent's ActionLanguage
		InterpreterImpl* invoked = _invokedInterpreter.getImpl().get();
		ActionLanguage* alOrig = _callbacks->getActionLanguage();
		if (alOrig != NULL) {
			ActionLanguage al;
			// create new instances
			al.execContent = alOrig->execContent.getImpl()->create(invoked);
			al.delayQueue = alOrig->delayQueue.getImplDelayed()->create(invoked);
			al.internalQueue = alOrig->internalQueue.getImplBase()->create();
			al.externalQueue = alOrig->externalQueue.getImplBase()->create();
			al.microStepper = alOrig->microStepper.getImpl()->create(invoked);
			/**
			 * TODO: Do we want a clone of the logger or the same instance?
			 */
			al.logger = alOrig->logger.getImpl()->create();
			// Note: we do not create a new instance from the existing datamodel as it may be of a different type

			_invokedInterpreter.setActionLanguage(al);
		}
		// TODO: setup invokers dom, check datamodel attribute and create new instance from parent if matching?

		// copy monitors
		std::set<InterpreterMonitor*> monitors = _callbacks->getMonitors();
		for (auto monitor : monitors) {
			if (monitor->copyToInvokers()) {
				_invokedInterpreter.getImpl()->_monitors.insert(monitor);
			}
		}

		_isActive = true;

		// we need to make sure it is at least setup to receive data!
		_invokedInterpreter.getImpl()->init();

		start();

	} else {
		// test 530
		// TODO: Is this the correct thing/place to do?
		Event e("done.invoke." + invokeEvent.invokeid, Event::PLATFORM);
		eventToSCXML(e, USCXML_INVOKER_SCXML_TYPE, _invokeId);
		_isActive = false;
	}
}

void USCXMLInvoker::ParentQueueImpl::enqueue(const Event& event) {
	// test 252
	if (!_invoker->_isActive)
		return;
	Event copy(event); // TODO: can we get around a copy?
	_invoker->eventToSCXML(copy, USCXML_INVOKER_SCXML_TYPE, _invoker->_invokeId);
}

}
