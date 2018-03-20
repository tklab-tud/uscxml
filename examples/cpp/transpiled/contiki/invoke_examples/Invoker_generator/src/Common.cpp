#include "Common.h"
#include <string.h>


Common::Common()
{
}

Common::~Common()
{
}

 string Common::inputSourceFilename;
 string Common::inputSourceFilePath;
 string Common::headerFileName;
 string Common::processName;
 string Common::fullInputSourceFilename;
 string Common::fullHeaderFilename;
 string Common::invokerSourceFileName;
 string Common::invokerHeaderFileName;

std::string Common::extractFileNameFromPath(const std::string FileNameWithPath)
{
	const char *filePath = FileNameWithPath.c_str();
	char *fileDir; 
	char *fileName;
	char *fileExt;

#if defined _WIN32
	const char *lastSeparator = strrchr(filePath, '\\');
#else
	const char *lastSeparator = strrchr(filePath, '/');
#endif

	const char *lastDot = strrchr(filePath, '.');
	const char *startOfName = lastSeparator ? lastSeparator + 1 : filePath;
	/*const char *endOfPath = filePath + strlen(filePath);
	const char *startOfName = lastSeparator ? lastSeparator + 1 : filePath;
	const char *startOfExt = lastDot > startOfName ? lastDot : endOfPath;*/

	/*if (fileDir)
		_snprintf(fileDir, 260, "%.*s", startOfName - filePath, filePath);

	if (fileName)
		_snprintf(fileName, 260, "%.*s", startOfExt - startOfName, startOfName);	

	if (fileExt)
		_snprintf(fileExt, 260, "%s", startOfExt);*/

	//fileName = ((char*)(startOfExt - startOfName));
	std::string fileNameWithExt = startOfName;
	//fileNameWithExt = fileName;
	//fileNameWithExt.append(fileExt);
	return fileNameWithExt;
}

std::string Common::getInputSourceFilename()
{
	return inputSourceFilename;
}

void Common::setInputSourceFilename(std::string input_source_file_name)
{
	inputSourceFilename = input_source_file_name;
}

std::string Common::getInputSourceFilePath()
{
	return inputSourceFilePath;
}

void Common::setInputSourceFilePath(std::string input_Source_file_path)
{
	inputSourceFilePath = input_Source_file_path;
}

std::string Common::getHeaderFileName()
{
	return headerFileName;
}

void Common::setHeaderFileName(std::string header_file_name)
{
	headerFileName = header_file_name;
}

std::string Common::getProcessName()
{
	return processName;
}

void Common::setProcessName(std::string process_name)
{
	processName = process_name;
}

std::string Common::getfullInputSourceFilename()
{
	return fullInputSourceFilename;
}

void Common::setfullInputSourceFilename(std::string full_input_source_filename)
{
	fullInputSourceFilename = full_input_source_filename;
}

std::string Common::getFullHeaderFilename()
{
	return fullHeaderFilename;
}

void Common::setFullHeaderFilename(std::string full_header_filename)
{
	fullHeaderFilename = full_header_filename;
}

std::string Common::getInvokerSourceFileName()
{
	return invokerSourceFileName;
}

void Common::setInvokerSourceFileName(std::string invoker_source_file_name)
{
	invokerSourceFileName = invoker_source_file_name;
}

std::string Common::getInvokerHeaderFileName()
{
	return invokerHeaderFileName;
}

void Common::setInvokerHeaderFileName(std::string invoker_header_file_name)
{
	invokerHeaderFileName = invoker_header_file_name;
}
