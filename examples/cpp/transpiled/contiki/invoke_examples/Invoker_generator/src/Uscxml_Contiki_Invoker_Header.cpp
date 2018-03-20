#include "Uscxml_Contiki_Invoker_Header.h"
#include "Common.h"
#include "sstream" //For std::stringstream
#include "string" //For std::string
#include "iostream" //For std::cout
#include <algorithm> // For std::transform

Invoker_Header::Invoker_Header(std::string output_file_name)
{
	Invoker_Header::outputFile = output_file_name;
}

Invoker_Header::~Invoker_Header()
{
}

string Invoker_Header::generateInvokerHeaderName()
{
	string name = "contiki_";
	name += Common::getInputSourceFilename().substr(0, Common::getInputSourceFilename().length() - 2);
	name += "_Invoker.h";
	return name;
}

int Invoker_Header::generateContent()
{
	outFile.open(outputFile);
	string content;
	std::stringstream contentStream;
	string processName = Common::getProcessName();
	string invokerHeaderFileName = Common::getInvokerHeaderFileName();
	string invokerHeaderFileNameUpper = invokerHeaderFileName;
	
	

	while (invokerHeaderFileNameUpper.find(".") != string::npos)
	{
		invokerHeaderFileNameUpper.replace(invokerHeaderFileNameUpper.find("."), 1, "_");
	}

	while (invokerHeaderFileNameUpper.find("-") != string::npos)
	{
		invokerHeaderFileNameUpper.replace(invokerHeaderFileNameUpper.find("-"), 1, "_");
	}
	
	string className = invokerHeaderFileNameUpper;
	transform(invokerHeaderFileNameUpper.begin(), invokerHeaderFileNameUpper.end(), invokerHeaderFileNameUpper.begin(), ::toupper);

	className = className.substr(0, className.length() - 2);

	contentStream \
		<< "#ifndef " << invokerHeaderFileNameUpper << "\n" \
		<< "#define " << invokerHeaderFileNameUpper << "\n \n" \
		<< "#include \"uscxml/config.h\"" << "\n"\
		<< "#include \"uscxml/plugins/InvokerImpl.h\"" << "\n \n" \
		<< "#ifdef __cplusplus" << "\n" \
		<< " #define EXTERNC extern \"C\"" << "\n" \
		<< "#else" << "\n" \
		<< " #define EXTERNC " << "\n" \
		<< "#endif" << "\n \n" \
		<< "EXTERNC{" << "\n" \
		<< "#include \"" << Common::getHeaderFileName() << "\"" << "\n" \
		<< "}" << "\n\n" \
		<< "namespace uscxml {" << "\n" \
		<< "\t" << "class " << className << " : public InvokerImpl {" << "\n" \
		<< "\t" << "public:" << "\n" \
		<< "\t\t" << className << "();" << "\n" \
		<< "\t\t" << "virtual ~" << className << "();" << "\n" \
		<< "\t\t" << "virtual std::shared_ptr<InvokerImpl> create(uscxml::InvokerCallbacks* callbacks);" << "\n" \
		<< "\t\t" << "virtual std::list<std::string> getNames() {" << "\n" \
		<< "\t\t\t" << "std::list<std::string> names;" << "\n" \
		<< "\t\t\t" << "names.push_back(\"uscxml_contiki/" /* same line continues*/ \
		<< Common::getHeaderFileName().substr(0, Common::getHeaderFileName().length() - 2) << "\");" << "\n" \
		<< "\t\t\t" << "names.push_back(\"contiki/" /* same line continues*/ \
		<< Common::getHeaderFileName().substr(0, Common::getHeaderFileName().length() - 2) << "\");" << "\n" \
		<< "\t\t\t" << "names.push_back(\"" /* same line continues*/ \
		<< Common::getHeaderFileName().substr(0, Common::getHeaderFileName().length() - 2) << "\");" << "\n" \
		<< "\t\t\t" << "return names;" << "\n" \
		<< "\t\t" << "}" << "\n" \
		<< "\t\t" << "virtual Data getDataModelVariables();" << "\n" \
		<< "\t\t" << "virtual void eventFromSCXML(const Event& event);" << "\n" \
		<< "\t\t" << "virtual void invoke(const std::string& source, const Event& invokeEvent);" << "\n" \
		<< "\t\t" << "virtual void uninvoke();" << "\n" \
		<< "\t" << "};" << "\n" \
		<< "}" << "\n" \
		<< "#endif /* end of include guard: " << invokerHeaderFileNameUpper << "*/";

	content = contentStream.str();
	std::cout << "Content " << content;
	outFile << content << endl;

	return 0;
}
//
//#ifndef CONTIKIHELLOWORLDINVOKER_H_OQFA21JO
//#define CONTIKIHELLOWORLDINVOKER_H_OQFA21JO
//
//#include "uscxml/config.h"
//#include "uscxml/plugins/InvokerImpl.h"
//
//#ifdef __cplusplus
//#define EXTERNC extern "C"
//#else
//#define EXTERNC
//#endif
////#define HELLOWORLD_CONTIKIINVOKER
//#ifdef HELLOWORLD_CONTIKIINVOKER
//EXTERNC{
//#include "hello-world.h"
//}
//#endif
//
//namespace uscxml {
//
//	/**
//	* @ingroup invoker
//	* An invoker for other calc instances.
//	*/
//	class CONTIKIHelloworldInvoker : public InvokerImpl {
//
//	public:
//		CONTIKIHelloworldInvoker();
//		virtual ~CONTIKIHelloworldInvoker();
//		virtual std::shared_ptr<InvokerImpl> create(uscxml::InvokerCallbacks* callbacks);
//
//		virtual std::list<std::string> getNames() {
//			std::list<std::string> names;
//			names.push_back("contiki");
//			names.push_back("contiki_helloworld");
//			names.push_back("helloworld");
//			return names;
//		}
//
//		virtual Data getDataModelVariables();
//		virtual void eventFromSCXML(const Event& event);
//		virtual void invoke(const std::string& source, const Event& invokeEvent);
//		virtual void uninvoke();
//	};
//}
//#endif /* end of include guard: CONTIKIHELLOWORLDINVOKER_H_OQFA21JO */

