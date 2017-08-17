#include <string>
#include <iostream> //For std::cout, std::endl
#include "Source_Parser.h"
#include "Common.h"

using namespace std;
Source_Parser::Source_Parser(std::string input_file_name, std::string output_file_name)
{
	Source_Parser::inputFile = input_file_name;
	Source_Parser::outputFile = output_file_name;
}

Source_Parser::~Source_Parser()
{
}

int Source_Parser::parse() {

	inFile.open(inputFile);
	outFile.open(outputFile);
	string strOneLine;
	string processName;
	bool header_included = false;
	while (inFile)
	{
		getline(inFile, strOneLine);

		if (strOneLine.find("AUTOSTART_PROCESSES") != std::string::npos) {
			strOneLine = "";
		}

		if (strOneLine.find(Common::getHeaderFileName()) != std::string::npos && header_included) {
			strOneLine = "";
		}

		if (strOneLine.find("#include") != std::string::npos && !header_included) {
		//Common::getHeaderFileName()
			strOneLine += "\n";
			strOneLine += "#include \"";
			strOneLine += Common::getHeaderFileName();
			strOneLine += "\"";
			header_included = true;
		}

		if (strOneLine.find("PROCESS(") != std::string::npos) {
			processName = strOneLine;
			processName = processName.substr(processName.find("(")+1, (processName.find(",")- processName.find("(")-1));
			Common::setProcessName(processName);
		}
		cout << strOneLine << endl;
		outFile << strOneLine<<endl;
	}
	
	outFile.close();
	inFile.close();

	return 0;
}



//Code to extract each word out of a line.
//if (!inFile.good())
//	return 1; // exit if file not found

//			  // read each line of the file
//while (!inFile.eof())
//{
//	// read an entire line into memory
//	char buf[MAX_CHARS_PER_LINE];
//	inFile.getline(buf, MAX_CHARS_PER_LINE);

//	// parse the line into blank-delimited tokens
//	int n = 0; // a for-loop index

//	// array to store memory addresses of the tokens in buf
//	const char* token[MAX_TOKENS_PER_LINE] = {}; // initialize to 0

//												 // parse the line
//	token[0] = strtok(buf, DELIMITER); // first token
//	if (token[0]) // zero if line is blank
//	{
//		for (n = 1; n < MAX_TOKENS_PER_LINE; n++)
//		{
//			token[n] = strtok(0, DELIMITER); // subsequent tokens
//			if (!token[n]) break; // no more tokens
//		}
//	}

//	// process (print) the tokens
//	for (int i = 0; i < n; i++) // n = #of tokens
//		std::cout << "Token[" << i << "] = " << token[i] << std::endl;
//	std::cout << std::endl;
//}