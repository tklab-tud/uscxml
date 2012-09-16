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

  Interpreter* scxml = Interpreter::fromURI(argv[1]);
  scxml->start();
  scxml->waitForStabilization();
  
  Event event1;
  event1.name = "event1";
  scxml->receive(event1);
  scxml->waitForStabilization();
  while(true)
    tthread::this_thread::sleep_for(tthread::chrono::milliseconds(200));
  
}