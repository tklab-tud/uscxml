#include "uscxml/Interpreter.h"

int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "Expected path to test-execution.scxml" << std::endl;
    exit(EXIT_FAILURE);
  }
  
  using namespace uscxml;
  using namespace Arabica::DOM;
  using namespace Arabica::XPath;
  
  Interpreter* interpreter = new Interpreter(argv[1]);
  interpreter->dump();
  interpreter->interpret();
}