#include "uscxml/config.h"
#include "uscxml/server/Socket.h"
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

class TestServer : public ServerSocket {
public:
	TestServer(int domain, int type, int protocol) : ServerSocket(domain, type, protocol) {}
	virtual void readCallback(const char* data, size_t size, Connection& conn) {
		std::string content(data, size);
//		std::cout << "Server got: " << content << std::endl;
		std::string urghs("hi!");
		conn.reply(urghs.data(), urghs.size());
	};
};

class TestClient : public ClientSocket {
public:
	TestClient(int domain, int type, int protocol) : ClientSocket(domain, type, protocol) {}
	virtual void readCallback(const char* data, size_t size) {
		std::string content(data, size);
	};
};

int main(int argc, char** argv) {

#if defined(HAS_SIGNAL_H) && !defined(WIN32)
	signal(SIGPIPE, SIG_IGN);
#endif

#ifndef _WIN32
	evthread_use_pthreads();
#else
	evthread_use_windows_threads();
#endif

//	TestClient client(PF_INET, SOCK_STREAM, 0);
//	client.connect("epikur.local", 4343);
	
	StartRequest startReq;
	startReq.source = "undefined.source";
	startReq.target = "epikur.local:4343";
	startReq.requestId = "131234141234";
	startReq.data =
		"<vxml xmlns=\"http://www.w3.org/2001/vxml\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" version=\"2.1\" xml:lang=\"en\""
		"xsi:schematicLocation=\"http://www.w3.org/2001/vxml http://www.w3.org/TR/voicexml20/vxml.xsd\">"
		"	<prompt>Goodbye!</prompt>"
		"</vxml>";

	Arabica::DOM::Document<std::string> reqXML = startReq.toXML();
	std::stringstream xmlSS;
	xmlSS << reqXML;
	std::cout << reqXML;
	
//	client.write(xmlSS.str().data(), xmlSS.str().size());
}