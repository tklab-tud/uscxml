#include "uscxml/Interpreter.h"
#include "uscxml/server/HTTPServer.h"
#include <sstream>

extern "C" {
#include "jsmn.h" // minimal json parser
}

#include <event2/keyvalq_struct.h>
#include <event2/buffer.h>

/**
 POST /foo HTTP/1.1
 host: localhost:9000
 accept: application/json
 content-type: application/json
 content-length: 92
 Connection: keep-alive

 {"load":"http://localhost:9999/scxml-test-framework/test/targetless-transition/test3.scxml"}
*/

class TestIOProcessor : public uscxml::HTTPServlet, public uscxml::InterpreterMonitor {
public:

	static int lastToken;
	static bool alreadyAnswered; // we need this for delayed events
	static std::map<std::string, std::pair<uscxml::Interpreter*, uscxml::HTTPServer::Request> > _interpreters;

	TestIOProcessor() {}

	virtual void beforeCompletion(uscxml::Interpreter* interpreter) {
		onStableConfiguration(interpreter);
	}

	virtual void afterCompletion(uscxml::Interpreter* interpreter) {
		_interpreters[interpreter->getName()].second.curlReq = NULL;
	}
	virtual void beforeMicroStep(uscxml::Interpreter* interpreter) {}
	virtual void beforeTakingTransitions(uscxml::Interpreter* interpreter, const Arabica::XPath::NodeSet<std::string>& transitions) {}

	virtual void beforeEnteringStates(uscxml::Interpreter* interpreter, const Arabica::XPath::NodeSet<std::string>& statesToEnter) {
		std::cout << "Entering states: ";
		for (int i = 0; i < statesToEnter.size(); i++) {
			std::cout << ATTR(statesToEnter[i], "id") << ", ";
		}
		std::cout << std::endl;
	}

	virtual void afterEnteringStates(uscxml::Interpreter* interpreter) {
		std::cout << "After entering states: ";
		for (int i = 0; i < interpreter->getConfiguration().size(); i++) {
			std::cout << ATTR(interpreter->getConfiguration()[i], "id") << ", ";
		}
		std::cout << std::endl;
	}

	virtual void beforeExitingStates(uscxml::Interpreter* interpreter, const Arabica::XPath::NodeSet<std::string>& statesToExit) {
		std::cout << "Configuration: ";
		for (int i = 0; i < interpreter->getConfiguration().size(); i++) {
			std::cout << ATTR(interpreter->getConfiguration()[i], "id") << ", ";
		}
		std::cout << std::endl;
		std::cout << "Exiting states: ";
		for (int i = 0; i < statesToExit.size(); i++) {
			std::cout << ATTR(statesToExit[i], "id") << ", ";
		}
		std::cout << std::endl;
	}

	virtual void afterExitingStates(uscxml::Interpreter* interpreter) {
		std::cout << "After exiting states: ";
		for (int i = 0; i < interpreter->getConfiguration().size(); i++) {
			std::cout << ATTR(interpreter->getConfiguration()[i], "id") << ", ";
		}
		std::cout << std::endl;
	}

	virtual void onStableConfiguration(uscxml::Interpreter* interpreter) {
		if (alreadyAnswered)
			return;

		Arabica::XPath::NodeSet<std::string> configuration = interpreter->getConfiguration();

		uscxml::Data reply;
		reply.compound["sessionToken"] = uscxml::Data(interpreter->getName());
		std::string seperator;
		for (size_t i = 0; i < configuration.size(); i++) {
			if (uscxml::Interpreter::isAtomic(configuration[i]))
				reply.compound["nextConfiguration"].array.push_back(uscxml::Data(ATTR(configuration[i], "id"), uscxml::Data::VERBATIM));
		}

		std::cout << "---- reply:" << std::endl;
		std::cout << reply << std::endl;

		std::stringstream replyString;
		replyString << reply;

		alreadyAnswered = true;

		uscxml::HTTPServer::Request httpRequest = _interpreters[interpreter->getName()].second;
		uscxml::HTTPServer::Reply httpReply(httpRequest);
		httpReply.content = replyString.str();
		uscxml::HTTPServer::reply(httpReply);

	}

	void httpRecvRequest(const uscxml::HTTPServer::Request& request) {

//    uscxml::HTTPServer::Reply httpReply(request);
//    uscxml::HTTPServer::reply(httpReply);
//    return;

		std::cout << "---- received:" << std::endl;
		evhttp_request_own(request.curlReq);

		std::cout << request.data.compound.at("content").atom << std::endl;
		uscxml::Data jsonReq = uscxml::Data::fromJSON(request.data.compound.at("content").atom);
		std::cout << jsonReq << std::endl;


		// is this a load request?
		if (jsonReq.compound.find("load") != jsonReq.compound.end()) {
			std::string filename = jsonReq.compound["load"].atom;
			std::cout << "Starting Interpreter with " << filename << std::endl;
			alreadyAnswered = false;

			std::map<std::string, std::pair<uscxml::Interpreter*, uscxml::HTTPServer::Request> >::iterator interpreterIter = _interpreters.begin();
			while(interpreterIter != _interpreters.end()) {
//        if (interpreterIter->second.second.curlReq == NULL) {
				delete interpreterIter->second.first;
				_interpreters.erase(interpreterIter++);
//        } else {
//          interpreterIter++;
//        }
			}


			uscxml::Interpreter* interpreter = uscxml::Interpreter::fromURI(filename);
			if (interpreter) {
				std::string token = uscxml::toStr(lastToken++);
				assert(_interpreters.find(token) == _interpreters.end());
				interpreter->setName(token);
				interpreter->addMonitor(this);
				interpreter->start();
				_interpreters[token] = std::make_pair(interpreter, request);
			}
			return;
		}

		if(jsonReq.compound.find("event") != jsonReq.compound.end()) {
			assert(jsonReq.compound["event"].compound.find("sessionToken") != jsonReq.compound["event"].compound.end());
			std::string token = jsonReq.compound["event"].compound["sessionToken"].atom;
			assert(_interpreters.find(token) != _interpreters.end());
			uscxml::Event event;
			event.type = uscxml::Event::INTERNAL;
			event.name = jsonReq.compound["event"].compound["name"].atom;
			std::cout << "Sending event " << event << std::endl;
//      evhttp_request_free(_interpreters[token].second);
			alreadyAnswered = false;
			_interpreters[token].second = request;
			_interpreters[token].first->receive(event);
		}

	}

	void setURL(const std::string& url) {
		std::cout << "Listening at " << url << std::endl;
	}
};

int TestIOProcessor::lastToken;
bool TestIOProcessor::alreadyAnswered;
std::map<std::string, std::pair<uscxml::Interpreter*, uscxml::HTTPServer::Request> > TestIOProcessor::_interpreters;

int main(int argc, char** argv) {
	TestIOProcessor* testServer = new TestIOProcessor();
	uscxml::HTTPServer::registerServlet("test", testServer);

	while(true)
		tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));

}