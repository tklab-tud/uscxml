#include "uscxml/plugins/DataModel.h"
#include "uscxml/plugins/datamodel/lua/LuaDataModel.h"
#include "uscxml/plugins/Factory.h"
#include "uscxml/interpreter/Logging.h"

#include <iostream>

using namespace std;
using namespace uscxml;

std::string test1 = "\
{ \n\
    [1] = { 1, 1, 1, 1 }, \n\
    [2] = { 2, 2, 2, 2 }, \n\
    [3] = { 3, 3 }, \n\
    [7] = false, \n\
    [8] = true \n\
}\
";

std::string test2 = "\
{ \
    zzz = { \
        [0] = { 1, 1, 1, 1 }, \
        [2] = { 5, 5, 5, 5 }, \
        [3] = { 10, 10 }, \
        [8] = { 80, 80 } \
    }, \
    bb = { \
        [3] = { 3, 3 }, \
        [2] = { 2, 2 } \
    } \
}\
";

std::string test3 = "\
{ \n\
    [2] = { \n\
        [1]={ 5,5,5,5 }, \n\
        [2]={ 5,5,5,5 }, \n\
        [3]= { 10,10 } \n\
    }, \n\
    [1] = { \n\
        [1]= { 4,4,4,4,4,4,4,4 }, \n\
        [2]= { 8,8,8,8 }, \n\
        [3]= { 16,16 } \n\
    }, \n\
    [3] = { \n\
        [1]={ 2,2,2 }, \n\
        test = false, \n\
        good = true, \n\
        xxx = 'asdf' \n\
    }, \n\
    zzz = { \n\
        1,2,3,\"different types\", \n\
        [[bbbbbbb\nbbbbbb]], \n\
        qq = \"asdf 'asdf' [[asdf]]\" \n\
    }\
}\
";

class DMCallbacks : public DataModelCallbacks {
public:
	std::string name = "asdf";
	std::string sessionId = "asdf";
	std::map<std::string, IOProcessor> ioProcs;
	std::map<std::string, Invoker> invokers;

	virtual ~DMCallbacks() {}
	const std::string& getName() {
		return name;
	}
	const std::string& getSessionId()  {
		return sessionId;
	}
	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return ioProcs;
	}
	virtual bool isInState(const std::string& stateId) {
		return false;
	}
	virtual XERCESC_NS::DOMDocument* getDocument() const {
		return nullptr;
	}
	virtual const std::map<std::string, Invoker>& getInvokers() {
		return invokers;
	}
	virtual Logger getLogger() {
		return Logger::getDefault();
	}

};

int main(int argc, char** argv) {
	try {
		DataModel lua = Factory::getInstance()->createDataModel("lua", new DMCallbacks());
		std::cout << "TEST1:" << lua.evalAsData(test1).asJSON() << std::endl << std::endl;
		std::cout << "TEST2:" << lua.evalAsData(test2).asJSON() << std::endl << std::endl;
		std::cout << "TEST3:" << lua.evalAsData(test3).asJSON() << std::endl << std::endl;

		{
			Data d1 = lua.evalAsData(test3);
			lua.assign("mixedTable", d1);
			Data d2 = lua.evalAsData("mixedTable");
			std::cout << "TEST3.2:" << d2.asJSON() << std::endl << std::endl;
			Data d3 = lua.evalAsData("mixedTable.zzz");
			std::cout << "TEST3.3:" << d3.asJSON() << std::endl << std::endl;
			Data d4 = lua.evalAsData("mixedTable[1]");
			std::cout << "TEST3.4:" << d4.asJSON() << std::endl << std::endl;

		}
	} catch (Event e) {
		std::cout << e << std::endl;
	}
}
