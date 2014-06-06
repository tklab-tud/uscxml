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

#include <uscxml/Interpreter.h>
#include <boost/enable_shared_from_this.hpp>
#include "uscxml/concurrency/BlockingQueue.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class Interpreter;
class USCXMLInvoker;

class USCXMLInvoker :
	public InvokerImpl,
	public boost::enable_shared_from_this<USCXMLInvoker> {
public:
	class ParentQueue : public concurrency::BlockingQueue<SendRequest> {
	public:
		ParentQueue() {}
		virtual void push(const SendRequest& event);
		USCXMLInvoker* _invoker;
	};

	USCXMLInvoker();
	virtual ~USCXMLInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);
	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("scxml");
		names.push_back("uscxml");
		names.push_back("http://www.w3.org/TR/scxml");
		names.push_back("http://www.w3.org/TR/scxml/");
		return names;
	}

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void cancel(const std::string sendId);
	virtual void invoke(const InvokeRequest& req);

protected:
	bool _cancelled;
	ParentQueue _parentQueue;
	Interpreter _invokedInterpreter;
	InterpreterImpl* _parentInterpreter;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(USCXMLInvoker, InvokerImpl);
#endif

}

#endif /* end of include guard: USCXMLINVOKER_H_OQFA21IO */
