#include "uscxml/Interpreter.h"
#include <DOM/io/Stream.hpp>

int main(int argc, char** argv) {
	if (argc != 2) {
		std::cerr << "Expected path to test-communication.scxml" << std::endl;
		exit(EXIT_FAILURE);
	}


	using namespace uscxml;
	std::list<Interpreter*> _interpreters;

//  Event e;
//  e.compound["foo"] = Data("bar", Data::VERBATIM);
//  e.compound["foo2"] = Data("bar2", Data::VERBATIM);
//  std::cout << e.toDocument() << std::endl;

	int nrInterpreters = 1;
	for (int i = 0; i < nrInterpreters; i++) {
		_interpreters.push_back(Interpreter::fromURI(argv[1]));
		_interpreters.back()->start();
	}

	std::list<Interpreter*>::iterator interIter = _interpreters.begin();
	while(interIter != _interpreters.end()) {
		(*interIter)->join();
		interIter++;
	}

}