#pragma once
#include <string>

using namespace std;
class Common
{
public:
	Common();
	~Common();
	static std::string extractFileNameFromPath(std::string FileNameWithPath);

	static std::string getInputSourceFilename();
	static void setInputSourceFilename(std::string input_source_file_name);

	static std::string getInputSourceFilePath();
	static void setInputSourceFilePath(std::string input_Source_file_path);

	static std::string getHeaderFileName();
	static void setHeaderFileName(std::string header_file_name);

	static std::string getProcessName();
	static void setProcessName(std::string process_name);

	static std::string getfullInputSourceFilename();
	static void setfullInputSourceFilename(std::string full_input_source_filename);

	static std::string getFullHeaderFilename();
	static void setFullHeaderFilename(std::string full_header_filename);

	static std::string getInvokerSourceFileName();
	static void setInvokerSourceFileName(std::string invoker_source_file_name);

	static std::string getInvokerHeaderFileName();
	static void setInvokerHeaderFileName(std::string invoker_header_file_name);

private:
	static string fullInputSourceFilename;
	static string inputSourceFilename;
	static string inputSourceFilePath;
	static string fullHeaderFilename;
	static string headerFileName;
	static string processName;
	static string invokerSourceFileName;
	static string invokerHeaderFileName;

};
