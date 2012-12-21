#include "uscxml/Interpreter.h"
#include "uscxml/plugins/datamodel/prolog/swi/SWIDataModel.h"

int main(int argc, char** argv) {
	if (argc != 2) {
		std::cerr << "Expected path to test-prolog.scxml" << std::endl;
		exit(EXIT_FAILURE);
	}

	using namespace uscxml;
	using namespace Arabica::DOM;
	using namespace Arabica::XPath;

	uscxml::Factory::pluginPath = "/Users/sradomski/Documents/TK/Code/uscxml/build/xcode/lib";
	Interpreter* scxml = Interpreter::fromURI(argv[1]);
//	scxml->start();
//	scxml->join();
//	tthread::this_thread::sleep_for(tthread::chrono::milliseconds(500));

}