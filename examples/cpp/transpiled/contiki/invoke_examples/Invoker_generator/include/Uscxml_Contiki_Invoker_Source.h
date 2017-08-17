#pragma once
#include <fstream> //For std::ifstream;
#include <string>

class Invoker_Source
{
public:
	Invoker_Source(std::string output_file_name);
	~Invoker_Source();
	static std::string generateInvokerName();
	int generateContent();

private:
	std::ofstream outFile;
	std::string outputFile;
};


