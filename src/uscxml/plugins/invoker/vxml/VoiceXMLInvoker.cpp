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

#include "VoiceXMLInvoker.h"
#include <glog/logging.h>
#include "uscxml/UUID.h"

#include <DOM/io/Stream.hpp>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define ISSUE_REQUEST(name) {\
	Arabica::DOM::Document<std::string> name##XML = name.toXML(true);\
	name##XML.getDocumentElement().setPrefix("mmi");\
	std::stringstream name##XMLSS;\
	name##XMLSS << name##XML;\
	URL name##URL(name.target);\
	std::cout << "SEND: " << name##XMLSS.str() << std::endl; \
	name##URL.setOutContent(name##XMLSS.str());\
	name##URL.addOutHeader("Content-type", "application/xml");\
	name##URL.download(false);\
}

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new VoiceXMLInvokerProvider() );
	return true;
}
#endif

VoiceXMLInvoker::VoiceXMLInvoker() {
	_thread = NULL;
}

VoiceXMLInvoker::~VoiceXMLInvoker() {
};

boost::shared_ptr<InvokerImpl> VoiceXMLInvoker::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<VoiceXMLInvoker> invoker = boost::shared_ptr<VoiceXMLInvoker>(new VoiceXMLInvoker());
	invoker->_interpreter = interpreter;
	return invoker;
}

bool VoiceXMLInvoker::httpRecvRequest(const HTTPServer::Request& request) {
	tthread::lock_guard<tthread::mutex> lock(_mutex);

	if (!request.data.hasKey("content") || !request.data.at("content").node) {
		HTTPServer::Reply reply(request);
		reply.status = 500;
		HTTPServer::reply(reply);
	}
	
	const Arabica::DOM::Node<std::string>& node = request.data.at("content").node;
	std::cout << "RCVD: " << node << std::endl;

	switch(MMIEvent::getType(node)) {
		case MMIEvent::NEWCONTEXTRESPONSE: {
			NewContextResponse resp = NewContextResponse::fromXML(node);
			if (_context.size() == 0) {
				_compState = MMI_IDLE;
				_context = resp.context;
				
				StartRequest startReq;
				startReq.context = _context;
				startReq.source = _url;
				startReq.target = _target;
				startReq.requestId = uscxml::UUID::getUUID();

				if (_invokeReq.src.size() > 0) {
					startReq.contentURL.href = _invokeReq.src;
				} else if(_invokeReq.content.size()) {
					startReq.content = _invokeReq.content;
				} else if(_invokeReq.dom) {
					std::stringstream contentSS;
					startReq.contentDOM = _invokeReq.dom;
				}
				ISSUE_REQUEST(startReq);

			} else {
				// already got a context!
			}
			break;
		}
		case MMIEvent::STARTRESPONSE: {
			StartResponse resp = StartResponse::fromXML(node);
			_compState = MMI_RUNNING;
			break;
		}

		case MMIEvent::DONENOTIFICATION: {
			DoneNotification resp = DoneNotification::fromXML(node);
			_compState = MMI_IDLE;
			break;
		}
	
		case MMIEvent::EXTENSIONNOTIFICATION: {
			ExtensionNotification resp = ExtensionNotification::fromXML(node);
			Event ev;
			ev.name = "mmi.extensionnotification";
			if (resp.dataDOM) {
				ev.dom = resp.dataDOM;
			} else if(resp.data.size() > 0) {
				ev.data = Data::fromJSON(resp.data); // try to parse as JSON
				if (ev.data.empty()) {
					ev.content = resp.data;
				}
			}
			returnEvent(ev);
		}
			
		default:
			break;
	}
	
	
	HTTPServer::Reply reply(request);
	HTTPServer::reply(reply);
	return true;
}

void VoiceXMLInvoker::setURL(const std::string& url) {
	_url = url;
}

Data VoiceXMLInvoker::getDataModelVariables() {
	Data data;
	return data;
}

void VoiceXMLInvoker::send(const SendRequest& req) {
	_workQueue.push(req);
}

void VoiceXMLInvoker::invoke(const InvokeRequest& req) {
	tthread::lock_guard<tthread::mutex> lock(_mutex);

	HTTPServer::getInstance()->registerServlet(req.invokeid, this);
	
	Event::getParam(req.params, "target", _target);
	if (_target.size() == 0) {
		LOG(ERROR) << "No target parameter given!";
		return;
	}
	
	_invokeReq = req;
	
	NewContextRequest newCtxReq;
	newCtxReq.source = _url;
	newCtxReq.target = _target;
	newCtxReq.requestId = uscxml::UUID::getUUID();
	ISSUE_REQUEST(newCtxReq);

	_isRunning = true;
	_thread = new tthread::thread(VoiceXMLInvoker::run, this);

}

void VoiceXMLInvoker::uninvoke() {
	
	ClearContextRequest clrCtxReq;
	clrCtxReq.source = _url;
	clrCtxReq.target = _target;
	clrCtxReq.requestId = uscxml::UUID::getUUID();
	ISSUE_REQUEST(clrCtxReq);

	if (_isRunning)
		_isRunning = false;
	
	SendRequest req;
	_workQueue.push(req);
	
	if (_thread) {
		_thread->join();
		delete _thread;
	}

	HTTPServer::getInstance()->unregisterServlet(this);
	_context = "";

}

void VoiceXMLInvoker::run(void* instance) {
	VoiceXMLInvoker* INSTANCE = (VoiceXMLInvoker*)instance;
	while(true) {
		SendRequest req = INSTANCE->_workQueue.pop();
		if (INSTANCE->_isRunning) {
			INSTANCE->process(req);
		} else {
			return;
		}
	}
}

void VoiceXMLInvoker::process(SendRequest& req) {
	tthread::lock_guard<tthread::mutex> lock(_mutex);
	while(_context.size() == 0 && _isRunning)
		_cond.wait_for(_mutex, 200);
	
	if (_context.size() == 0) {
		// we never acquired a context
		return;
	}
	
	// dispatch over send request

	
	// if we did nothing else, send as ExtensionNotification
	ExtensionNotification extNotif;
	extNotif.context = _context;
	extNotif.source = _url;
	extNotif.target = _target;
	extNotif.requestId = uscxml::UUID::getUUID();
	extNotif.name = req.name;

	if (!req.namelist.empty()) {
		for (Event::namelist_t::iterator iter = req.namelist.begin(); iter != req.namelist.end(); iter++) {
			req.data.compound[iter->first] = iter->second;
		}
	} else if (!req.params.empty()) {
		for(Event::params_t::iterator it = req.params.begin(), end = req.params.end(); it != end; it = req.params.upper_bound(it->first)) {
			Event::getParam(req.params, it->first, req.data.compound[it->first]);
		}
	}
	
	if (req.dom) {
		extNotif.dataDOM = req.dom;
	} else if (req.content.size() > 0) {
		extNotif.data = req.content;
	} else if (!req.data.empty()) {
		extNotif.data = Data::toJSON(req.data);
	}
	
	ISSUE_REQUEST(extNotif);

}
	
}