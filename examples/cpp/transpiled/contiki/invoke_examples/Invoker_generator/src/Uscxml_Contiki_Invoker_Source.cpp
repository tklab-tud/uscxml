#include "Uscxml_Contiki_Invoker_Source.h"
#include "Common.h"
#include "sstream" //For std::stringstream
#include "string" //For std::string
#include "iostream" //For std::cout

Invoker_Source::Invoker_Source(std::string output_file_name)
{
	Invoker_Source::outputFile = output_file_name;
}

Invoker_Source::~Invoker_Source()
{
}

string Invoker_Source::generateInvokerName()
{
	string name = "contiki_";
	name += Common::getInputSourceFilename().substr(0, Common::getInputSourceFilename().length() - 2);
	name += "_Invoker.cpp";
	return name;
}

//
//#include "CONTIKIHelloworldInvoker.h"
//#include "iostream"
//
//
//namespace uscxml {
//
//	CONTIKIHelloworldInvoker::CONTIKIHelloworldInvoker() {}
//	CONTIKIHelloworldInvoker::~CONTIKIHelloworldInvoker() {}
//
//	std::shared_ptr<InvokerImpl> CONTIKIHelloworldInvoker::create(uscxml::InvokerCallbacks* callbacks) {
//		std::shared_ptr<CONTIKIHelloworldInvoker> invoker(new CONTIKIHelloworldInvoker());
//		invoker->_callbacks = callbacks;
//		return invoker;
//	}
//
//	Data CONTIKIHelloworldInvoker::getDataModelVariables() {
//		Data data;
//		return data;
//	}
//	void CONTIKIHelloworldInvoker::eventFromSCXML(const Event& event) {}
//	void CONTIKIHelloworldInvoker::invoke(const std::string& source, const Event& invokeEvent) {
//		process_start(&ftp_process, NULL);
//	}
//
//	void CONTIKIHelloworldInvoker::uninvoke() {
//#ifdef FTP_CONTIKIINVOKER
//		if (process_is_running(&ftp_process))
//			process_exit(&ftp_process);
//#endif
//#ifdef CALC_CONTIKIINVOKER
//		if (process_is_running(&calc_process))
//			process_exit(&calc_process);
//#endif
//#ifdef SETTING_CONTIKIINVOKER
//		if (process_is_running(&settings_example_process))
//			process_exit(&settings_example_process);
//#endif
//
//	}
//}


int Invoker_Source::generateContent()
{
	outFile.open(outputFile);
	string content;
	std::stringstream contentStream;
	string processName = Common::getProcessName();
	string headerFileName = Common::getInvokerHeaderFileName();
	string className = headerFileName;
	className = className.substr(0, className.length() - 2);
	
	while (className.find(".") != string::npos)
	{
		className.replace(className.find("."), 1, "_");
	}

	while (className.find("-") != string::npos)
	{
		className.replace(className.find("-"), 1, "_");
	}

	contentStream \
		<< "#include \"" << headerFileName << "\" \n" \
		<< "#include \"iostream\"" << "\n \n" \
		<< "namespace uscxml {" << "\n \n" \
		<< className << "::" << className << "() {}" << "\n" \
		<< className << "::~" << className << "() {}" << "\n" \
		<< "std::shared_ptr<InvokerImpl> " << className << "::create(uscxml::InvokerCallbacks* callbacks) {" << "\n" \
		<< "\t" << "std::shared_ptr<" << className << "> invoker(new " << className << "());" << "\n" \
		<< "\t" << "invoker->_callbacks = callbacks;" << "\n"
		<< "\t" << "return invoker;" << "\n"
		<< "}" << "\n \n" \
		<< "Data " << className << "::getDataModelVariables() {" << "\n" \
		<< "\t" << "Data data;" << "\n"\
		<< "\t" << "return data;" << "\n" \
		<< "}" << "\n \n"
		<< "void " << className << "::eventFromSCXML(const Event& event) {}" << "\n" \
		<< "void " << className << "::invoke(const std::string& source, const Event& invokeEvent) {" << "\n" \
		<< "\t" << "process_start(&" << processName << ", NULL);" << "\n"
		<< "}" << "\n \n" \
		<< "void " << className << "::uninvoke() {	" << "\n" \
		<< "\t" << "if (process_is_running(&" << processName << "))" << "\n" \
		<< "\t \t" << "process_exit(&" << processName << ");" << "\n" \
		<< "\t" << "}" << "\n" \
		<< "}" << "\n";

	content = contentStream.str();
	std::cout << "Content " << content;
	outFile << content << endl;
	
	return 0;
}

