#pragma once

#include <fstream> //For std::ifstream;
//#include <cstring>


const int MAX_CHARS_PER_LINE = 512;
const int MAX_TOKENS_PER_LINE = 20;
const char* const DELIMITER = " ";

class Source_Parser
{
public:
	Source_Parser(std::string input_file_name, std::string output_file_name);
	~Source_Parser();
	int parse();
	

private:
	std::ifstream inFile;
	std::ofstream outFile;
	std::string inputFile;
	std::string outputFile;
	
};
