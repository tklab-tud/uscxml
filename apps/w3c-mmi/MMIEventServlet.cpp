#include "MMIEventServlet.h"
#include <uscxml/NameSpacingParser.h>

#ifdef _WIN32
#include <winsock2.h>
#include <windows.h>
#endif

#include "uscxml/Message.h"
#include <iostream>
#include <event2/dns.h>
#include <event2/buffer.h>
#include <event2/keyvalq_struct.h>

#include <string.h>

#include <io/uri.hpp>
#include <glog/logging.h>

#ifndef _WIN32
#include <netdb.h>
#include <arpa/inet.h>
#endif

#define MMI_HTTP_EVENT_CASE(type) \
else if (boost::iequals(mmiEvent.getLocalName(), #type)) { \
	monIter = _monitors.begin(); \
	while(monIter != _monitors.end()) { \
		(*monIter)->received(type::fromXML(mmiDoc)); \
		monIter++; \
	} \
}

namespace uscxml {
	
	using namespace Arabica::DOM;
	
	MMIEventServlet::MMIEventServlet(const std::string& path) : _path(path) {
		// register at http server
		bool success = HTTPServer::registerServlet(_path, this);
		assert(success);
	}
	
	MMIEventServlet::~MMIEventServlet() {
		HTTPServer* httpServer = HTTPServer::getInstance();
		httpServer->unregisterServlet(this);
	}
	
	void MMIEventServlet::send(const MMIEvent& mmiEvent) {
		URL url(mmiEvent.target);
		url.addMonitor(this);
		
		std::stringstream content;
		content << mmiEvent.toXML();
		url.setOutContent(content.str());
		url.download();
		
	}

	void MMIEventServlet::httpRecvRequest(const HTTPServer::Request& req) {

		// is this a request from a HTML browser?
		
		
		NameSpacingParser* parser = NameSpacingParser::fromXML(req.data.compound.at("content").atom);
		if (!parser) {
			evhttp_send_error(req.curlReq, 402, NULL);
			return;
		}
		
		Document<std::string> mmiDoc = parser->getDocument();
		std::cout << mmiDoc.getNamespaceURI() << std::endl;
		Node<std::string> mmiEvent = mmiDoc.getFirstChild();
		// get the first element
		while (mmiEvent && mmiEvent.getNodeType() != Node_base::ELEMENT_NODE) {
			mmiEvent = mmiEvent.getNextSibling();
		}
		// get the contained message
		if (boost::iequals(mmiEvent.getLocalName(), "mmi")) {
			mmiEvent = mmiEvent.getFirstChild();
			while (mmiEvent && mmiEvent.getNodeType() != Node_base::ELEMENT_NODE) {
				mmiEvent = mmiEvent.getNextSibling();
			}
		}
		std::cout << mmiEvent << std::endl;
		
		if (!mmiEvent) {
			evhttp_send_error(req.curlReq, 402, NULL);
			return;
		}

		std::set<MMIEventReceiver*>::iterator monIter;
		if (false) {}
		MMI_HTTP_EVENT_CASE(NewContextRequest)
		MMI_HTTP_EVENT_CASE(NewContextResponse)
		MMI_HTTP_EVENT_CASE(PrepareRequest)
		MMI_HTTP_EVENT_CASE(PrepareResponse)
		MMI_HTTP_EVENT_CASE(StartRequest)
		MMI_HTTP_EVENT_CASE(StartResponse)
		MMI_HTTP_EVENT_CASE(DoneNotification)
		MMI_HTTP_EVENT_CASE(CancelRequest)
		MMI_HTTP_EVENT_CASE(CancelResponse)
		MMI_HTTP_EVENT_CASE(PauseRequest)
		MMI_HTTP_EVENT_CASE(PauseResponse)
		MMI_HTTP_EVENT_CASE(ResumeRequest)
		MMI_HTTP_EVENT_CASE(ResumeResponse)
		MMI_HTTP_EVENT_CASE(ExtensionNotification)
		MMI_HTTP_EVENT_CASE(ClearContextRequest)
		MMI_HTTP_EVENT_CASE(ClearContextResponse)
		MMI_HTTP_EVENT_CASE(StatusRequest)
		MMI_HTTP_EVENT_CASE(StatusResponse)
		else {
			LOG(ERROR) << "Unknown MMI Event";
			evhttp_send_error(req.curlReq, 402, NULL);
			return;
		}
		
		evhttp_send_reply(req.curlReq, 204, NULL, NULL);

#if 0
		Event reqEvent = req;
		reqEvent.type = Event::EXTERNAL;
		bool scxmlStructFound = false;
		
		if (reqEvent.data.compound["header"].compound.find("Content-Type") != reqEvent.data.compound["header"].compound.end() &&
				boost::iequals(reqEvent.data.compound["header"].compound["Content-Type"].atom, "application/x-www-form-urlencoded")) {
			std::stringstream ss(reqEvent.data.compound["content"].atom);
			std::string term;
			while(std::getline(ss, term, '&')) {
				size_t split = term.find_first_of("=");
				if (split != std::string::npos) {
					std::string key = evhttp_decode_uri(term.substr(0, split).c_str());
					std::string value = evhttp_decode_uri(term.substr(split + 1).c_str());
					if (boost::iequals(key, "_scxmleventname")) {
						reqEvent.name = value;
					} else if (boost::iequals(key, "content")) {
						reqEvent.initContent(value);
					} else {
						reqEvent.data.compound[key] = value;
						reqEvent.params.insert(std::make_pair(key, value));
					}
				} else {
					// this is most likely wrong
					reqEvent.content = evhttp_decode_uri(term.c_str());
				}
			}
		} else {
			if (reqEvent.data.compound["header"].compound.find("_scxmleventstruct") != reqEvent.data.compound["header"].compound.end()) {
				// TODO: this looses all other information
				reqEvent = Event::fromXML(evhttp_decode_uri(reqEvent.data.compound["header"].compound["_scxmleventstruct"].atom.c_str()));
				scxmlStructFound = true;
			}
			if (reqEvent.data.compound["header"].compound.find("_scxmleventname") != reqEvent.data.compound["header"].compound.end()) {
				reqEvent.name = evhttp_decode_uri(reqEvent.data.compound["header"].compound["_scxmleventname"].atom.c_str());
			}
		}
		std::map<std::string, Data>::iterator headerIter = reqEvent.data.compound["header"].compound.begin();
		while(headerIter != reqEvent.data.compound["header"].compound.end()) {
			reqEvent.data.compound[headerIter->first] = Data(evhttp_decode_uri(headerIter->second.atom.c_str()), Data::VERBATIM);
			headerIter++;
		}
		
		
		/// test532
		if (reqEvent.name.length() == 0)
			reqEvent.name = "http." + req.data.compound.at("type").atom;
		
		if (!scxmlStructFound) {
			// get content into event
			reqEvent.data.compound["content"] = Data(req.content, Data::VERBATIM);
		}
		
		evhttp_send_reply(req.curlReq, 200, "OK", NULL);
#endif
	}
		
	void MMIEventServlet::downloadStarted(const URL& url) {}
	
	void MMIEventServlet::downloadCompleted(const URL& url) {
		std::map<std::string, std::pair<URL, SendRequest> >::iterator reqIter = _sendRequests.begin();
		while(reqIter != _sendRequests.end()) {
			if (reqIter->second.first == url) {
				_sendRequests.erase(reqIter);
				return;
			}
			reqIter++;
		}
		assert(false);
	}
	
	void MMIEventServlet::downloadFailed(const URL& url, int errorCode) {
		
		std::map<std::string, std::pair<URL, SendRequest> >::iterator reqIter = _sendRequests.begin();
		while(reqIter != _sendRequests.end()) {
			if (reqIter->second.first == url) {
				Event failEvent;
				failEvent.name = "error.communication";
//				returnEvent(failEvent);
				
				_sendRequests.erase(reqIter);
				return;
			}
			reqIter++;
		}
		assert(false);
		
	}
	
	
}