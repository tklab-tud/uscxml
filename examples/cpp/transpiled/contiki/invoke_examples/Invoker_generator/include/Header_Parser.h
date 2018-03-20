#pragma once
#include <fstream> //For std::ifstream;

class Header_Parser
{
public:
	Header_Parser(std::string input_file_name, std::string output_file_name);
	~Header_Parser();
	int parse();


private:
	std::ifstream inFile;
	std::ofstream outFile;
	std::string inputFile;
	std::string outputFile;
};
