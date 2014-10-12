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

#ifndef VOICEXMLINVOKER_H_W09J90F0
#define VOICEXMLINVOKER_H_W09J90F0

#include <uscxml/Interpreter.h>
#include <uscxml/messages/MMIMessages.h>
#include "uscxml/server/HTTPServer.h"

// #include <uscxml/plugins/ioprocessor/modality/MMIProtoBridge.h>

#ifdef BUILD_AS_PLUGINS
#include "uscxml/plugins/Plugins.h"
#endif

namespace uscxml {

class VoiceXMLInvoker : public InvokerImpl, public HTTPServlet {
public:
	enum ComponentState {
		MMI_IDLE,
		MMI_PAUSED,
		MMI_RUNNING,
		MMI_DEAD
	};

	VoiceXMLInvoker();
	virtual ~VoiceXMLInvoker();
	virtual boost::shared_ptr<InvokerImpl> create(InterpreterImpl* interpreter);

	virtual std::list<std::string> getNames() {
		std::list<std::string> names;
		names.push_back("vxml");
		names.push_back("voicexml");
		names.push_back("http://www.w3.org/TR/voicexml21/");
		return names;
	}

	bool deleteOnUninvoke() {
		return false;
	}

	bool httpRecvRequest(const HTTPServer::Request& request);
	void setURL(const std::string& url);

	virtual Data getDataModelVariables();
	virtual void send(const SendRequest& req);
	virtual void invoke(const InvokeRequest& req);
	virtual void uninvoke();

	static void run(void*);
	void process(SendRequest& ctx);

protected:
	std::string _url;
	std::string _context;
	std::string _target;

	InvokeRequest _invokeReq;

	ComponentState _compState;

	tthread::thread* _thread;
	tthread::condition_variable _cond;
	tthread::mutex _mutex;
	concurrency::BlockingQueue<SendRequest> _workQueue;
	bool _isRunning;
};

#ifdef BUILD_AS_PLUGINS
PLUMA_INHERIT_PROVIDER(VoiceXMLInvoker, InvokerImpl);
#endif

}


#endif /* end of include guard: VOICEXMLINVOKER_H_W09J90F0 */
