#include "uscxml/Message.h"
#include "uscxml/Interpreter.h"
#include <assert.h>
#include <boost/algorithm/string.hpp>
#include <iostream>

using namespace uscxml;
using namespace boost;


int main(int argc, char** argv) {
#ifdef _WIN32
	WSADATA wsaData;
	WSAStartup(MAKEWORD(2, 2), &wsaData);
#endif

	if (argc != 2) {
		std::cerr << "Expected path to test-initial-config.scxml" << std::endl;
		exit(EXIT_FAILURE);
	}

	std::string test = argv[1];

	{
		Interpreter interpreter = Interpreter::fromURI(test);
		std::vector<std::string> states;
		states.push_back("finish_shortcut");
		states.push_back("ADMINISTRATIVE_NON-HR-MANAGEMENT");
		states.push_back("HR-MANAGER_MANAGE-HR");
		states.push_back("SYSTEM_1.1_BEGIN");
		states.push_back("COORDINATOR_1");
		interpreter.setConfiguration(states);
		interpreter.interpret();
	}

}