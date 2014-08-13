#include "uscxml/config.h"
#include "uscxml/server/Socket.h"
#include "uscxml/UUID.h"
#include <iostream>
#include <stdexcept>

#include <event2/event.h>
#include "event2/thread.h"

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#include "uscxml/concurrency/tinythread.h"
#include "uscxml/plugins/ioprocessor/modality/MMIMessages.h"
#include <DOM/io/Stream.hpp>

#include "uscxml/plugins/ioprocessor/modality/MMIMessages.cpp"


using namespace uscxml;

bool testAddressParsing() {
	std::string protocol;
	std::string hostName;
	uint16_t port;
	
	{
		Socket::parseAddress("4343", protocol, hostName, port);
		assert(protocol == "tcp");
		assert(hostName	== "127.0.0.1");
		assert(port	== 4343);
		
		Socket::parseAddress("localhost:4343", protocol, hostName, port);
		assert(protocol == "tcp");
		assert(hostName	== "localhost");
		assert(port	== 4343);
		
		Socket::parseAddress("tcp://localhost:4343", protocol, hostName, port);
		assert(protocol == "tcp");
		assert(hostName	== "localhost");
		assert(port	== 4343);
	}
	return true;
}

bool testMMIEvents() {
	{
		NewContextRequest newCtxReq;
		newCtxReq.source = "localhost:3434";
		newCtxReq.target = "localhost:1212";
		newCtxReq.requestId = "requestId";

		Arabica::DOM::Document<std::string> newCtxReqXML1 = newCtxReq.toXML();
		Arabica::DOM::Document<std::string> newCtxReqXML2 = newCtxReq.toXML(true);
		
//		std::cout << newCtxReqXML1 << std::endl;
//		std::cout << newCtxReqXML2 << std::endl;
		
		NewContextRequest newCtxReq1 = NewContextRequest::fromXML(newCtxReqXML1.getDocumentElement());
		NewContextRequest newCtxReq2 = NewContextRequest::fromXML(newCtxReqXML2.getDocumentElement());
		
		assert(MMIEvent::getType(newCtxReqXML1.getDocumentElement()) == MMIEvent::NEWCONTEXTREQUEST);
		assert(MMIEvent::getType(newCtxReqXML2.getDocumentElement()) == MMIEvent::NEWCONTEXTREQUEST);
		
		assert(newCtxReq1.source == "localhost:3434");
		assert(newCtxReq2.source == "localhost:3434");
		assert(newCtxReq1.target == "localhost:1212");
		assert(newCtxReq2.target == "localhost:1212");
		assert(newCtxReq1.requestId == "requestId");
		assert(newCtxReq2.requestId == "requestId");

	}
	return true;
}

class TestServer : public PacketServerSocket {
public:
	TestServer(int domain, int type, int protocol) : PacketServerSocket(domain, type, protocol, std::string("\0", 1)) {}
	virtual void readCallback(const std::string& packet, Connection& conn) {
		std::cout << "Server got: " << packet << std::endl;
		std::string urghs("hi!");
		conn.reply(urghs.data(), urghs.size());
	};

	std::stringstream fragment;
};

class TestClient : public ClientSocket {
public:
	TestClient(int domain, int type, int protocol) : ClientSocket(domain, type, protocol) {}
	virtual void readCallback(const char* data, size_t size) {
		std::string content(data, size);
	};
};

std::map<std::string, MMIEvent*> _requests;
std::map<std::string, MMIEvent*> _replies;

int main(int argc, char** argv) {

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

#ifndef _WIN32
	evthread_use_pthreads();
#else
	evthread_use_windows_threads();
#endif
	testAddressParsing();
	testMMIEvents();
	
//	TestClient client(PF_INET, SOCK_STREAM, 0);
//	client.connect("epikur.local", 4343);
	std::string target = "localhost:4343";
	std::string source = "localhost:4344";
	
	TestServer server(PF_INET, SOCK_STREAM, 0);
	server.listen(source);
	
//	while(true)
//		sleep(1000);
	
	TestClient client(PF_INET, SOCK_STREAM, 0);
	client.connect(source);
	
	NewContextRequest newCtxReq;
	newCtxReq.source = source;
	newCtxReq.target = target;
	newCtxReq.requestId = UUID::getUUID();
	
	_requests[newCtxReq.requestId] = &newCtxReq;
	
	Arabica::DOM::Document<std::string> newCtxReqXML = newCtxReq.toXML(true);
	std::stringstream newCtxReqXMLSS;
	newCtxReqXMLSS << newCtxReqXML;

	for (int i = 0; i < 100000; i++) {
		std::string index = toStr(i);
		client.write(index.c_str(), index.size() + 1);
//		client.write(newCtxReqXMLSS.str().data(), newCtxReqXMLSS.str().size());
//		client.write("\0", 1);
	}
	
	while(true)
		sleep(1000);

//	StartRequest startReq;
//	startReq.source = "localhost:4344";
//	startReq.target = "localhost:4343";
//	startReq.requestId = "131234141234";
//	startReq.data =
//	    "<vxml xmlns=\"http://www.w3.org/2001/vxml\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" version=\"2.1\" xml:lang=\"en\""
//	    "xsi:schematicLocation=\"http://www.w3.org/2001/vxml http://www.w3.org/TR/voicexml20/vxml.xsd\">"
//	    "	<prompt>Goodbye!</prompt>"
//	    "</vxml>";
//
//	Arabica::DOM::Document<std::string> reqXML = startReq.toXML();
//	std::stringstream xmlSS;
//	xmlSS << reqXML;
//	std::cout << reqXML;

//	client.write(xmlSS.str().data(), xmlSS.str().size());
}