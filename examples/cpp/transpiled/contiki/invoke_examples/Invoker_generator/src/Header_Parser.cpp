#include <string>
#include <sstream>
#include <iostream> //For std::cout, std::endl
#include "Header_Parser.h"
#include "Common.h"
#include <algorithm>

Header_Parser::Header_Parser(std::string input_file_name, std::string output_file_name)
{
	Header_Parser::inputFile = input_file_name;
	Header_Parser::outputFile = output_file_name;
}

Header_Parser::~Header_Parser()
{
}

int Header_Parser::parse()
{
	inFile.open(inputFile);
	outFile.open(outputFile);
	string strOneLine;
	string content;
	string headerFile = Common::getHeaderFileName();

	transform(headerFile.begin(), headerFile.end(), headerFile.begin(), ::toupper);
	
	while (headerFile.find(".") != string::npos)
	{
		headerFile.replace(headerFile.find("."), 1, "_");
	}

	while (headerFile.find("-") != string::npos)
	{
		headerFile.replace(headerFile.find("-"), 1, "_");
	}
	
	
	string processName = Common::getProcessName();
	std::stringstream contentStream;

	if (inFile) {
		contentStream << "#ifndef __" << headerFile << "__\n" << "#define __" << headerFile << "__\n"  \
			<< "#include \"contiki.h\" \n \n" << "PROCESS_NAME(" << processName << ");\n" << "#endif /* __" \
			<< headerFile << "__ */ \n";

		content = contentStream.str();
		
	}
	else
	{
		contentStream << "#ifndef __ " << headerFile << "__\n" << "#define __" << headerFile << "__\n"  \
			<< "#include \"contiki.h\" \n \n" << "PROCESS_NAME("<< processName<<");\n"<<"#endif /* __" \
			<< headerFile <<"__ */ \n";
		
		content = contentStream.str();
		
	}

	outFile << content << endl;
	outFile.close();
	inFile.close();

	return 0;
}

//Sample of generated file : 
//#ifndef __SETTING_EXAMPLE_H__
//#define __SETTING_EXAMPLE_H__
//#include "contiki.h"
//#define EEPROM_CONF_SIZE 1024
//
//		PROCESS_NAME(settings_example_process);
//#endif /* __SETTING_EXAMPLE_H__ */


