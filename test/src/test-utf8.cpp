#include "uscxml/config.h"
#include "uscxml/Interpreter.h"
#include "uscxml/plugins/Factory.h"
#include "uscxml/plugins/DataModelImpl.h"

#include <iostream>
#include <cassert>

/*
#define WITH_DM_ECMA_V8
#define WITH_DM_ECMA_JSC
#define WITH_DM_LUA
#define WITH_DM_PYTHON
#define WITH_DM_C89
#define WITH_DM_PROMELA
*/

using namespace uscxml;

class TestDataModelCallbacks : public DataModelCallbacks {
public:
	std::string _name = "name";
	std::string _sessionId = "sessionId";
	std::map<std::string, IOProcessor> _ioProcs;
	std::map<std::string, Invoker> _invokers;

	const std::string& getName() {
		return _name;
	}
	const std::string& getSessionId() {
		return _sessionId;
	}
	const std::map<std::string, IOProcessor>& getIOProcessors() {
		return _ioProcs;
	}
	virtual bool isInState(const std::string& stateId) {
		return true;
	}
	XERCESC_NS::DOMDocument* getDocument() const {
		return NULL;
	}
	const std::map<std::string, Invoker>& getInvokers() {
		return _invokers;
	}
	Logger getLogger() {
		return Logger::getDefault();
	}

};

TestDataModelCallbacks dmCallbacks;
std::list<std::string> datamodels;

bool testSimpleJSON() {
	for (auto dmName : datamodels) {
		std::cout << "** " << dmName << ":" << std::endl;
		DataModel dm = Factory::getInstance()->createDataModel(dmName, &dmCallbacks);
		Data json = Data::fromJSON("{\"ü\": \"ä\"}");
		dm.init("foo", json);
		Data json2 = dm.evalAsData("foo");
		std::cout << json << std::endl;
		std::cout << json2 << std::endl;
		assert(json == json2);

		dm.init("bar", Data("ö", Data::VERBATIM));
		bool cmp = dm.evalAsBool("bar == \"ö\"");
		std::cout << dm.evalAsData("bar") << std::endl;
		assert(cmp);

	}
	return true;
}


int main(int argc, char** argv) {
#ifdef WITH_DM_LUA
	datamodels.push_back("lua");
#endif
#ifdef WITH_DM_PROMELA
//    datamodels.push_back("promela");
#endif
#if (defined WITH_DM_ECMA_V8 || defined WITH_DM_ECMA_JSC)
	datamodels.push_back("ecmascript");
#endif

	testSimpleJSON();
	return EXIT_SUCCESS;
}
