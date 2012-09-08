#include "uscxml/Interpreter.h"
#include "uscxml/datamodel/ecmascript/v8/V8DataModel.h"

int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "Expected path to test-ecmascript.scxml" << std::endl;
    exit(EXIT_FAILURE);
  }

  using namespace uscxml;
  using namespace Arabica::DOM;
  using namespace Arabica::XPath;
  
//  class SCXMLRunner : public Thread {
//  public:
//    SCXMLRunner(Runtime* runtime) : _runtime(runtime) {}
//    void run() {
//      _runtime->interpret();
//    }
//    
//    Runtime* _runtime;
//  };
  
//  boost::shared_ptr<V8DataModel> v8 = boost::static_pointer_cast<V8DataModel>(Factory::create("datamodel:ecmascript", Arabica::DOM::Node<std::string>()));
//  v8->eval("var x = 4;");
//  assert(v8->evalAsBool("x == 4"));
//  assert(!v8->evalAsBool("x == 5"));
  
  Interpreter* scxml = new Interpreter(argv[1]);
  scxml->dump();
//  scxml->interpret();
  scxml->start();
  scxml->waitForStabilization();
  
  Event event1;
  event1.name = "event1";
  scxml->receive(event1);
  scxml->waitForStabilization();
  tthread::this_thread::sleep_for(tthread::chrono::milliseconds(200));
  
//  SCXMLRunner* scxmlRun = new SCXMLRunner(scxmlRuntime);
//  scxmlRun->start();
  
}