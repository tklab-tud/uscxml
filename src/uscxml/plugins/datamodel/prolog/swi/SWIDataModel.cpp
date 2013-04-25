#include "uscxml/Common.h"
#include "uscxml/config.h"
#include "SWIDataModel.h"
#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool connect(pluma::Host& host) {
	host.add( new SWIDataModelProvider() );
	return true;
}
#endif

SWIDataModel::SWIDataModel() {
}

boost::shared_ptr<DataModelImpl> SWIDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SWIDataModel> dm = boost::shared_ptr<SWIDataModel>(new SWIDataModel());
	dm->_interpreter = interpreter;

	const char* swibin = getenv("SWI_BINARY");
	if (swibin == NULL)
		swibin = SWI_BINARY;
	const char* quiet = "--quiet";

	static char * av[] = {
		(char*)swibin,
		(char*)quiet,
		//    "-s",
		//    "/Users/sradomski/Documents/TK/Code/pl-devel/demo/likes.pl",
		NULL
	};
	if(!PL_initialise(2,av)) {
		LOG(ERROR) << "Error intializing prolog engine";
		PL_halt(1);
		return boost::shared_ptr<DataModelImpl>();
	}

	// load SWI XML parser
	PlCall("use_module", PlCompound("library", PlTerm("sgml")));
	PlCall("assert", PlCompound("sessionId", PlTerm(PlString(dm->_interpreter->getSessionId().c_str()))));
	PlCall("assert", PlCompound("name", PlTerm(PlString(dm->_interpreter->getName().c_str()))));

	PlCall("assert(eventName(X) :- event(Y,_), arg(1, Y, X)).");
	return dm;
}

void SWIDataModel::registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor) {
//	std::cout << "SWIDataModel::registerIOProcessor" << std::endl;
}

void SWIDataModel::setSessionId(const std::string& sessionId) {
//	std::cout << "SWIDataModel::setSessionId" << std::endl;
	_sessionId = sessionId;
}

void SWIDataModel::setName(const std::string& name) {
//	std::cout << "SWIDataModel::setName" << std::endl;
	_name = name;
}

SWIDataModel::~SWIDataModel() {
}

void SWIDataModel::pushContext() {
//	std::cout << "SWIDataModel::pushContext" << std::endl;
}

void SWIDataModel::popContext() {
//	std::cout << "SWIDataModel::popContext" << std::endl;
}

void SWIDataModel::initialize() {
//	std::cout << "SWIDataModel::initialize" << std::endl;
}

void SWIDataModel::setEvent(const Event& event) {
	// remove old event
	PlCall("system", "retractall", PlTermv("event"));
	
	PlTermv plEvent(7);
	plEvent[0] = PlCompound("name", PlTerm(PlString(event.name.c_str())));
	plEvent[1] = PlCompound("raw", PlTerm(PlString(event.raw.c_str())));
	plEvent[2] = PlCompound("origin", PlTerm(PlString(event.origin.c_str())));
	plEvent[3] = PlCompound("origintype", PlTerm(PlString(event.origintype.c_str())));
	plEvent[4] = PlCompound("data", PlTerm(PlString(event.content.c_str())));
	
	Event::params_t::const_iterator paramIter;
	// count unique keys in params
	paramIter = event.params.begin();
	size_t uniqueKeys = 0;
	while(paramIter != event.params.end()) {
		uniqueKeys++;
		paramIter = event.params.upper_bound(paramIter->first);
	}
	
	// create a compund for every unique key
	PlTermv paramTerm(uniqueKeys);
	paramIter = event.params.begin();
	for(int i = 0; paramIter != event.params.end(); i++) {
		Event::params_t::const_iterator	lastValueIter = event.params.upper_bound(paramIter->first);
		size_t items = event.params.count(paramIter->first);
		PlTermv keyTerm(items);
		for (int j = 0; paramIter != lastValueIter; j++) {
			keyTerm[j] = PlString(paramIter->second.c_str());
			paramIter++;
		}
		paramTerm[i] = PlCompound(paramIter->first.c_str(), keyTerm);
		paramIter = lastValueIter;
	}
	plEvent[5] = PlCompound("params", paramTerm);
	
	PlTerm type;
	switch (event.type) {
		case Event::PLATFORM:
			type = "platform";
			break;
		case Event::INTERNAL:
			type = "internal";
			break;
		case Event::EXTERNAL:
			type = "external";
			break;
	}
	plEvent[6] = PlCompound("type", type);
	PlCall("assert", PlCompound("event", plEvent));
}

Data SWIDataModel::getStringAsData(const std::string& content) {
//	std::cout << "SWIDataModel::getStringAsData" << std::endl;
	Data data;
	return data;
}

bool SWIDataModel::validate(const std::string& location, const std::string& schema) {
//	std::cout << "SWIDataModel::validate" << std::endl;
	return true;
}

uint32_t SWIDataModel::getLength(const std::string& expr) {
//	std::cout << "SWIDataModel::getLength" << std::endl;
	return 0;
}

void SWIDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
	//	std::cout << "SWIDataModel::setForeach" << std::endl;
}

void SWIDataModel::eval(const std::string& expr) {
	URL localPLFile = URL::toLocalFile(expr, ".pl");
	PlCall("user", "load_files", PlTermv(localPLFile.asLocalFile(".pl").c_str())) || LOG(ERROR) << "Could not execute prolog from file";
}

bool SWIDataModel::evalAsBool(const std::string& expr) {
	PlCompound compound(expr.c_str());
	PlTermv termv(compound.arity());
	for (int i = 0; i < compound.arity(); i++) {
		termv[i] = compound[i + 1];
	}
	PlQuery query(compound.name(), termv);
	return query.next_solution() > 0;
}

std::string SWIDataModel::evalAsString(const std::string& expr) {
	PlCompound compound(expr.c_str());
	if (strlen(compound.name())) {
		PlTermv termv(compound.arity());
		for (int i = 0; i < compound.arity(); i++) {
			termv[i] = compound[i + 1];
		}
		PlQuery query(compound.name(), termv);

		std::stringstream ss;
		const char* separator = "";
		while (query.next_solution()) {
			for (int i = 0; i < compound.arity(); i++) {
				ss << separator << (char *)termv[i];
				separator = ", ";
			}
		}
		return ss.str();
	}
	return std::string(compound);
}

void SWIDataModel::assign(const Arabica::DOM::Element<std::string>& assignElem,
                          const Arabica::DOM::Document<std::string>& doc,
                          const std::string& content) {
	std::string expr = content;
	if (HAS_ATTR(assignElem, "expr")) {
		expr = ATTR(assignElem, "expr");
	}
	if (expr.length() > 0)
		eval(expr);
}

void SWIDataModel::assign(const std::string& location, const Data& data) {
	eval(data.atom);
}

void SWIDataModel::init(const Arabica::DOM::Element<std::string>& dataElem,
                        const Arabica::DOM::Document<std::string>& doc,
                        const std::string& content) {
	std::string key;
	if (HAS_ATTR(dataElem, "id")) {
		key = ATTR(dataElem, "id");
	} else if (HAS_ATTR(dataElem, "location")) {
		key = ATTR(dataElem, "location");
	}
	assign(dataElem, doc, content);
}
void SWIDataModel::init(const std::string& location, const Data& data) {}

bool SWIDataModel::isDeclared(const std::string& expr) {
	return true;
}

}
