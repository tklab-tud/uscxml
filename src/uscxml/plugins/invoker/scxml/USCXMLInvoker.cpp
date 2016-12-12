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

#include "uscxml/config.h"

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
};

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
		state = INSTANCE->_invokedInterpreter.step();

//		if (!INSTANCE->_isStarted) {
//			// we have been cancelled
//			INSTANCE->_isActive = false;
//			return;
//		}
	}

	if (INSTANCE->_isActive) {
		// we finished on our own and were not cancelled
		Event e;
		e.eventType = Event::PLATFORM;
		e.invokeid = INSTANCE->_invokedInterpreter.getImpl()->getInvokeId();
		e.name = "done.invoke." + e.invokeid;
		INSTANCE->_interpreter->enqueueExternal(e);
	}

	INSTANCE->_isActive = false;
}

std::shared_ptr<InvokerImpl> USCXMLInvoker::create(InterpreterImpl* interpreter) {
	std::shared_ptr<USCXMLInvoker> invoker(new USCXMLInvoker());
	invoker->_interpreter = interpreter;
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

//        std::cout << *document << std::endl;

		// TODO: where do we get the namespace from?
		_invokedInterpreter = Interpreter::fromDocument(document, _interpreter->getBaseURL(), false);

	} else {
		_isActive = false;
		ERROR_PLATFORM_THROW("Cannot invoke nested SCXML interpreter, neither src attribute nor content nor DOM is given");
	}

	if (_invokedInterpreter) {
		_invokedInterpreter.getImpl()->_parentQueue = _parentQueue;
		_invokedInterpreter.getImpl()->_invokeId = invokeEvent.invokeid;
		_invokedInterpreter.getImpl()->_invokeReq = invokeEvent;

		// create new instances from the parent's ActionLanguage
#if 1
		InterpreterImpl* invoked = _invokedInterpreter.getImpl().get();
		invoked->_execContent = _interpreter->_execContent.getImpl()->create(invoked);
		invoked->_delayQueue = _interpreter->_delayQueue.getImplDelayed()->create(invoked);
		invoked->_internalQueue = _interpreter->_internalQueue.getImplBase()->create();
		invoked->_externalQueue = _interpreter->_externalQueue.getImplBase()->create();
		invoked->_microStepper = _interpreter->_microStepper.getImpl()->create(invoked);

		// TODO: setup invokers dom, check datamodel attribute and create new instance from parent if matching?
#endif
		// copy monitors
		std::set<InterpreterMonitor*>::const_iterator monIter = _interpreter->_monitors.begin();
		while(monIter != _interpreter->_monitors.end()) {
			if ((*monIter)->copyToInvokers()) {
				_invokedInterpreter.getImpl()->_monitors.insert(*monIter);
			}
			monIter++;
		}

		/**
		 * test240 assumes that invoke request params will carry over to the datamodel
		 * This is solved by passing the invoke request above
		 */
//		_invokedInterpreter.getImpl()->setInvokeRequest(req);
		_isActive = true;

		// we need to make sure it is at least setup to receive data!
		_invokedInterpreter.getImpl()->init();

		start();

	} else {
		/// test 530
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
