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

#ifndef COMETIOPROCESSOR_H_2CUY93KU
#define COMETIOPROCESSOR_H_2CUY93KU

#include "uscxml/concurrency/eventqueue/DelayedEventQueue.h"
#include "uscxml/server/HTTPServer.h"
#include "uscxml/Interpreter.h"
#include "uscxml/Factory.h"

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class CometIOProcessor : public IOProcessorImpl, public HTTPServlet {
public:
	CometIOProcessor();
	virtual ~CometIOProcessor();
	virtual boost::shared_ptr<IOProcessorImpl> create(uscxml::InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("comet");
		names.push_back("http://www.w3.org/TR/scxml/#CometEventProcessor");
		return names;
	}

	/// This method can be overridden for specific replies
	virtual void reply(const SendRequest& req, const HTTPServer::Request& longPoll);

	virtual void send(const SendRequest& req);
	Data getDataModelVariables();

	virtual bool httpRecvRequest(const HTTPServer::Request& request);
	virtual void setURL(const std::string& url) {
		_url = url;
	}

protected:
	tthread::recursive_mutex _mutex;
	std::string _url;
	std::deque<SendRequest> _outQueue;
	HTTPServer::Request _longPollingReq;

};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(CometIOProcessor, IOProcessorImpl);
#endif

}

#endif /* end of include guard: COMETIOPROCESSOR_H_2CUY93KU */