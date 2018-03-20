#pragma once
#include <fstream> //For std::ifstream;
#include <string>

class Invoker_Header
{
public:
	Invoker_Header(std::string output_file_name);
	~Invoker_Header();
	static std::string generateInvokerHeaderName();
	int generateContent();

private:
	std::ofstream outFile;
	std::string outputFile;
};


