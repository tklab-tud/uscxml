#include <iostream>
#include "Source_Parser.h"
#include "Header_Parser.h"
#include "Uscxml_Contiki_Invoker_Source.h"
#include "Uscxml_Contiki_Invoker_Header.h"
#include "Common.h"

using namespace std;

string getHeaderFile() {
	string fullHeaderfileName; //read from config.
	if (fullHeaderfileName.empty()) {
		fullHeaderfileName = Common::getInputSourceFilename();
		fullHeaderfileName.replace(fullHeaderfileName.find(".c"), fullHeaderfileName.length(), ".h");
	}
	return fullHeaderfileName;
}

void init(string f) {
	string filename = f;
	Common::setfullInputSourceFilename(filename);
	Common::setInputSourceFilename(Common::extractFileNameFromPath(Common::getfullInputSourceFilename()));
	Common::setFullHeaderFilename(getHeaderFile());
	Common::setHeaderFileName(Common::extractFileNameFromPath(Common::getFullHeaderFilename()));
	Common::setInvokerSourceFileName(Invoker_Source::generateInvokerName());
	Common::setInvokerHeaderFileName(Invoker_Header::generateInvokerHeaderName());
}


int main(int argc, char* argv[])
{
	// Check the number of parameters
	if (argc < 2) {
		// Tell the user how to run the program
		std::cerr << "Usage: " << argv[0] << "please provide absolute Path to invoker process source file as command line argument" << std::endl;
		return 1;
	}
	
	string filename = argv[1];
		
	std::cout << "filename = " + filename << std::endl;
	init(filename);

	Source_Parser s(Common::getfullInputSourceFilename(),Common::getInputSourceFilename());
	Header_Parser h(Common::getFullHeaderFilename(), Common::getHeaderFileName());
	Invoker_Source i_s(Common::getInvokerSourceFileName());
	Invoker_Header i_h(Common::getInvokerHeaderFileName());
	
	s.parse();
	h.parse();
	i_s.generateContent();
	i_h.generateContent();
}
