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

#ifndef USCXMLINVOKER_H_OQFA21IO
#define USCXMLINVOKER_H_OQFA21IO

#include "uscxml/config.h"
#include "uscxml/interpreter/InterpreterImpl.h"
#include "uscxml/interpreter/BasicEventQueue.h"

#include "uscxml/plugins/InvokerImpl.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

#define USCXML_INVOKER_SCXML_TYPE "http://www.w3.org/TR/scxml"

namespace uscxml {

/**
* @ingroup invoker
 * An invoker for other SCXML instances.
 */
class USCXMLInvoker :
	public InvokerImpl,
	public std::enable_shared_from_this<USCXMLInvoker> {
public:
	class ParentQueueImpl : public BasicEventQueue {
	public:
		ParentQueueImpl(USCXMLInvoker* invoker) : _invoker(invoker) {}
		virtual void enqueue(const Event& event);
		USCXMLInvoker* _invoker;
	};

	USCXMLInvoker();
	virtual ~USCXMLInvoker();
	virtual std::shared_ptr<InvokerImpl> create(InvokerCallbacks* callbacks);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("scxml");
		names.push_back("uscxml");
		names.push_back(USCXML_INVOKER_SCXML_TYPE);
		names.push_back("http://www.w3.org/TR/scxml/");
		return names;
	}

	virtual void eventFromSCXML(const Event& event);

	virtual Data getDataModelVariables();
	virtual void invoke(const std::string& source, const Event& invokeEvent);
	virtual void uninvoke();

	virtual void deserialize(const Data& encodedState);
	virtual Data serialize();

protected:

	void start();
	void stop();
	static void run(void* instance);

	bool _isActive;
	bool _isStarted;
	std::thread* _thread;
	EventQueue _parentQueue;
	Interpreter _invokedInterpreter;

	std::recursive_mutex _mutex;
	std::condition_variable_any _cond;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(USCXMLInvoker, InvokerImpl)
#endif

}

#endif /* end of include guard: USCXMLINVOKER_H_OQFA21IO */
