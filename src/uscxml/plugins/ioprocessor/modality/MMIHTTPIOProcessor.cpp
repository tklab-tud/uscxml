#include "uscxml/plugins/ioprocessor/modality/MMIHTTPIOProcessor.h"
#include "uscxml/Message.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new MMIHTTPIOProcessorProvider() );
	return true;
}
#endif

MMIHTTPIOProcessor::MMIHTTPIOProcessor() {
}

MMIHTTPIOProcessor::~MMIHTTPIOProcessor() {
}

boost::shared_ptr<IOProcessorImpl> MMIHTTPIOProcessor::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<MMIHTTPIOProcessor> io = boost::shared_ptr<MMIHTTPIOProcessor>(new MMIHTTPIOProcessor());
	io->_interpreter = interpreter;

	// register at http server
	std::string path = interpreter->getName();
	int i = 2;
	while (!HTTPServer::registerServlet(path + "/mmihttp", io.get())) {
		std::stringstream ss;
		ss << interpreter->getName() << i++;
		path = ss.str();
	}

	return io;
}

bool MMIHTTPIOProcessor::httpRecvRequest(const HTTPServer::Request& req) {
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

#if 0
	std::map<std::string, std::string>::const_iterator headerIter = req.headers.begin();
	while(headerIter != req.headers.end()) {
		if (boost::iequals("_scxmleventstruct", headerIter->first)) {
			reqEvent = Event::fromXML(evhttp_decode_uri(headerIter->second.c_str()));
			scxmlStructFound = true;
			break;
		} else if (boost::iequals("_scxmleventname", headerIter->first)) {
			reqEvent.name = evhttp_decode_uri(headerIter->second.c_str());
		} else {
			reqEvent.data.compound[headerIter->first] = Data(evhttp_decode_uri(headerIter->second.c_str()), Data::VERBATIM);
		}
		headerIter++;
	}
#endif

	/// test532
	if (reqEvent.name.length() == 0)
		reqEvent.name = "http." + req.data.compound.at("type").atom;

	if (!scxmlStructFound) {
		// get content into event
		reqEvent.data.compound["content"] = Data(req.content, Data::VERBATIM);
	}

	returnEvent(reqEvent);
	evhttp_send_reply(req.curlReq, 200, "OK", NULL);
	return true;
}

void MMIHTTPIOProcessor::send(const SendRequest& req) {

	if (req.target.length() == 0) {
		_interpreter->receiveInternal(Event("error.communication", Event::PLATFORM));
		return;
	}

	bool isLocal = false;
	std::string target;
	if (!boost::equals(req.target, _url)) {
		target = req.target;
	} else {
		isLocal = true;
		target = _url;
	}
	URL targetURL(target);
	std::stringstream kvps;
	std::string kvpSeperator;

	// event name
	if (req.name.size() > 0) {
		kvps << kvpSeperator << evhttp_encode_uri("_scxmleventname") << "=" << evhttp_encode_uri(req.name.c_str());
		kvpSeperator = "&";
//		targetURL.addOutHeader("_scxmleventname", evhttp_encode_uri(req.name.c_str()));
	}

	// event namelist
	if (req.namelist.size() > 0) {
		std::map<std::string, std::string>::const_iterator namelistIter = req.namelist.begin();
		while (namelistIter != req.namelist.end()) {
			kvps << kvpSeperator << evhttp_encode_uri(namelistIter->first.c_str()) << "=" << evhttp_encode_uri(namelistIter->second.c_str());
			kvpSeperator = "&";
//			targetURL.addOutHeader(namelistIter->first, namelistIter->second);
			namelistIter++;
		}
	}

	// event params
	if (req.params.size() > 0) {
		std::multimap<std::string, std::string>::const_iterator paramIter = req.params.begin();
		while (paramIter != req.params.end()) {
			kvps << kvpSeperator << evhttp_encode_uri(paramIter->first.c_str()) << "=" << evhttp_encode_uri(paramIter->second.c_str());
			kvpSeperator = "&";
//			targetURL.addOutHeader(paramIter->first, paramIter->second);
			paramIter++;
		}
	}

	// content

	if (req.content.size() > 0) {
		kvps << kvpSeperator << evhttp_encode_uri("content") << "=" << evhttp_encode_uri(req.content.c_str());
		kvpSeperator = "&";
	}
	if (req.dom) {
		std::stringstream xmlStream;
		xmlStream << req.dom;
		kvps << kvpSeperator << evhttp_encode_uri("content") << "=" << evhttp_encode_uri(xmlStream.str().c_str());
		kvpSeperator = "&";
	}
	targetURL.setOutContent(kvps.str());

	targetURL.setRequestType("post");
	targetURL.addMonitor(this);

	_sendRequests[req.sendid] = std::make_pair(targetURL, req);
	if (isLocal) {
		// test201 use a blocking request with local communication
		targetURL.download(true);
	} else {
		URLFetcher::fetchURL(targetURL);
	}
}



}