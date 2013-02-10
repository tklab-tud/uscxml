#include "uscxml/Interpreter.h"
#include "uscxml/plugins/ioprocessor/basichttp/libevent/EventIOProcessor.h"
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

class TestIOProcessor : public uscxml::EventIOProcessor, public uscxml::InterpreterMonitor {
public:


  static int lastToken;
  static std::map<std::string, std::pair<uscxml::Interpreter*, evhttp_request*> > _interpreters;

  TestIOProcessor() {}
  
  virtual void onStableConfiguration(uscxml::Interpreter* interpreter) {
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
    
    struct evbuffer *databuf = evbuffer_new();
    evbuffer_add(databuf, replyString.str().c_str(), replyString.str().length());
    evhttp_send_reply(_interpreters[interpreter->getName()].second, 200, "OK", databuf);
    evbuffer_free(databuf);

  }

  virtual void beforeCompletion(uscxml::Interpreter* interpreter) {}
  virtual void afterCompletion(uscxml::Interpreter* interpreter) {}
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
  
  virtual void httpRecvReq(struct evhttp_request *req) {
    
    std::cout << "---- received:" << std::endl;

    if (evhttp_request_get_command(req) != EVHTTP_REQ_POST)
      return;
    
    evhttp_request_own(req);

    struct evkeyval *header;
    struct evkeyvalq *headers;
    headers = evhttp_request_get_input_headers(req);
    
    for (header = headers->tqh_first; header;
         header = header->next.tqe_next) {
//      std::cout << header->key << ": " << header->value << std::endl;
    }

    std::string content;
    struct evbuffer *buf;
		buf = evhttp_request_get_input_buffer(req);
		while (evbuffer_get_length(buf)) {
			int n;
			char cbuf[128];
			n = evbuffer_remove(buf, cbuf, sizeof(buf)-1);
			if (n > 0) {
				content.append(cbuf, n);
			}
		}
    
    uscxml::Data jsonReq = uscxml::Data::fromJSON(content);
    std::cout << jsonReq << std::endl;
    
    
    // is this a load request?
    if (jsonReq.compound.find("load") != jsonReq.compound.end()) {
      std::string filename = jsonReq.compound["load"].atom;
      std::cout << "Starting Interpreter with " << filename << std::endl;
      uscxml::Interpreter* interpreter = uscxml::Interpreter::fromURI(filename);
      if (interpreter) {
        std::string token = uscxml::toStr(lastToken++);
        assert(_interpreters.find(token) == _interpreters.end());
        interpreter->setName(token);
        interpreter->addMonitor(this);
        interpreter->start();
        _interpreters[token] = std::make_pair(interpreter, req);
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
      _interpreters[token].second = req;
      _interpreters[token].first->receive(event);
    }
    
  }
  
  std::string getPath() {
    return "test";
  }
  
  void setURL(const std::string& url) {
    std::cout << "Listening at " << url << std::endl;
    _url = url;
  }
};

int TestIOProcessor::lastToken;
std::map<std::string, std::pair<uscxml::Interpreter*, evhttp_request*> > TestIOProcessor::_interpreters;

int main(int argc, char** argv) {
  TestIOProcessor* testServer = new TestIOProcessor();
  uscxml::EventIOServer::registerProcessor(testServer);

  while(true)
    tthread::this_thread::sleep_for(tthread::chrono::milliseconds(20));
  
//	uscxml::Interpreter* interpreter = uscxml::Interpreter::fromURI(argv[1]);
//	interpreter->dump();
//	interpreter->interpret();
}