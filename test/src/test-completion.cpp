#include "uscxml/Interpreter.h"
#include <DOM/io/Stream.hpp>

int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "Expected path to scxml document" << std::endl;
    exit(EXIT_FAILURE);
  }
  
  using namespace uscxml;

  Interpreter* interpreter = Interpreter::fromURI(argv[1]);
	interpreter->interpret();
	
	return EXIT_SUCCESS;
}