#include "uscxml/config.h"
#include "uscxml/UUID.h"
#include <iostream>
#include <stdexcept>

#include <boost/algorithm/string.hpp>

#include <event2/event.h>
#include "event2/thread.h"

#ifdef HAS_SIGNAL_H
#include <signal.h>
#endif

#include "uscxml/server/HTTPServer.h"
#include "uscxml/URL.h"
#include "uscxml/concurrency/tinythread.h"
#include "uscxml/messages/MMIMessages.h"
#include <DOM/io/Stream.hpp>

#ifdef _WIN32
#include "XGetopt.h"
#endif

#define ISSUE_REQUEST(name) {\
	Arabica::DOM::Document<std::string> name##XML = name.toXML(true);\
	name##XML.getDocumentElement().setPrefix("mmi");\
	std::stringstream name##XMLSS;\
	name##XMLSS << name##XML;\
	URL name##URL(target);\
	std::cout << "SEND:" << std::endl << name##XMLSS.str() << std::flush;\
	name##URL.setOutContent(name##XMLSS.str());\
	name##URL.addOutHeader("Content-type", "application/xml");\
	name##URL.download(false);\
}

using namespace uscxml;

std::map<std::string, MMIEvent*> Requests;
std::map<std::string, MMIEvent*> Replies;

tthread::condition_variable Cond;
tthread::mutex Mutex;

std::string context;

class MMIServlet : public HTTPServlet {
public:
	bool httpRecvRequest(const HTTPServer::Request& request) {
		std::cout << "RCVD:" << std::endl << request << std::flush;
		tthread::lock_guard<tthread::mutex> lock(Mutex);
		
		const Arabica::DOM::Document<std::string>& doc = request.data.at("content").node.getOwnerDocument();
//		NameSpacingParser parser = NameSpacingParser::fromXML(request.content);
		switch(MMIEvent::getType(doc.getDocumentElement())) {
			case MMIEvent::NEWCONTEXTRESPONSE: {
				NewContextResponse* resp = new NewContextResponse(NewContextResponse::fromXML(doc.getDocumentElement()));
				context = resp->context;
				Replies[resp->requestId] = resp;
				break;
			}
			case MMIEvent::STARTRESPONSE: {
				StartResponse* resp = new StartResponse(StartResponse::fromXML(doc.getDocumentElement()));
				Replies[resp->requestId] = resp;
			}
			default: ;
		}
		
		Cond.notify_all();
		
		HTTPServer::Reply reply(request);
		HTTPServer::reply(reply);
		
		return true;
	}
	void setURL(const std::string& url) {
		this->url = url;
	}
	std::string url;
};

void printUsageAndExit(const char* progName) {
	// remove path from program name
	std::string progStr(progName);
	if (progStr.find_last_of(PATH_SEPERATOR) != std::string::npos) {
		progStr = progStr.substr(progStr.find_last_of(PATH_SEPERATOR) + 1, progStr.length() - (progStr.find_last_of(PATH_SEPERATOR) + 1));
	}
	
	printf("%s version " USCXML_VERSION " (" CMAKE_BUILD_TYPE " build - " CMAKE_COMPILER_STRING ")\n", progStr.c_str());
	printf("Usage\n");
	printf("\t%s", progStr.c_str());
	printf(" [-tURL] URL");
	printf("\n");
	printf("Options\n");
	printf("\t-tURL       : URL of VoiceXML HTTP server\n");
	printf("\tURL         : URL of a VoiceXML document\n");
	printf("\n");
	exit(1);
}

int main(int argc, char** argv) {
	try {
		tthread::lock_guard<tthread::mutex> lock(Mutex);

		std::string target;
		std::string document;
		
		if (argc < 2)
			printUsageAndExit(argv[0]);

		int option;
		while ((option = getopt(argc, argv, "t:")) != -1) {
			switch(option) {
				case 't':
					target = optarg;
					break;
				default:
					printUsageAndExit(argv[0]);
			}
		}
		
		if (argc < optind)
			printUsageAndExit(argv[0]);
			
		document = argv[optind];
		
		if (!boost::starts_with(document, "http"))
			document = "http://" + document;

		if (!boost::starts_with(target, "http"))
			document = "http://" + target;

		// target = "http://130.83.163.167:9090/mmi";
		// target = "http://localhost:9090/mmi";

		
		MMIServlet servlet;
		HTTPServer::getInstance(4344, 0);
		HTTPServer::getInstance()->registerServlet("/mmi", &servlet);
		
		std::string source = servlet.url;

		NewContextRequest newCtxReq;
		newCtxReq.source = source;
		newCtxReq.target = target;
		newCtxReq.requestId = uscxml::UUID::getUUID();
			
		Requests[newCtxReq.requestId] = &newCtxReq;
		ISSUE_REQUEST(newCtxReq);

		while(Replies.find(newCtxReq.requestId) == Replies.end())
			Cond.wait(Mutex);
			
		StartRequest startReq;
		startReq.context = context;
		startReq.source = source;
		startReq.target = target;
		startReq.requestId = uscxml::UUID::getUUID();
		startReq.contentURL.href = document;
		//"https://raw.githubusercontent.com/Roland-Taizun-Azhar/TaskAssistance-Project/master/WebContent/hello.vxml";
		
		Requests[startReq.requestId] = &startReq;
		ISSUE_REQUEST(startReq);

		while(Replies.find(startReq.requestId) == Replies.end())
			Cond.wait(Mutex);
	} catch (Event e) {
		std::cout << e << std::endl;
	} catch (std::exception e) {
		std::cout << e.what() << std::endl;
	}
	
	
}