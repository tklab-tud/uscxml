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

// SWI prolog does not support passing user data
static InterpreterImpl* _swiInterpreterPtr;
	
boost::shared_ptr<DataModelImpl> SWIDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<SWIDataModel> dm = boost::shared_ptr<SWIDataModel>(new SWIDataModel());
	dm->_interpreter = interpreter;

	// this is most unfortunate!
	_swiInterpreterPtr = interpreter;
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

	// set system variables
	PlCall("assert", PlCompound("sessionid", PlTerm(PlString(dm->_interpreter->getSessionId().c_str()))));
	PlCall("assert", PlCompound("name", PlTerm(PlString(dm->_interpreter->getName().c_str()))));

	std::map<std::string, IOProcessor>::const_iterator ioProcIter = dm->_interpreter->getIOProcessors().begin();
	while(ioProcIter != dm->_interpreter->getIOProcessors().end()) {
		Data ioProcData = ioProcIter->second.getDataModelVariables();

		if (ioProcIter->first.find_first_of(":/'") == std::string::npos) {
			std::stringstream ioProcShortCall;
			ioProcShortCall << "assert(ioprocessors(" << ioProcIter->first << "(location('" << ioProcData.compound["location"].atom << "'))))";
			PlCall(ioProcShortCall.str().c_str());
		}
		std::stringstream ioProcCall;
		ioProcCall << "assert(ioprocessors(name('" << ioProcIter->first << "'), location('" << ioProcData.compound["location"].atom << "')))";
		PlCall(ioProcCall.str().c_str());

		ioProcIter++;
	}

	// the in predicate
	PlRegister("user", "in", 1, SWIDataModel::inPredicate);
	return dm;
}

foreign_t SWIDataModel::inPredicate(term_t a0, int arity, void* context) {
	char *s;
	if ( PL_get_atom_chars(a0, &s) ) {
		Arabica::XPath::NodeSet<std::string> config = _swiInterpreterPtr->getConfiguration();
		for (int i = 0; i < config.size(); i++) {
			if (HAS_ATTR(config[i], "id") && strcmp(ATTR(config[i], "id").c_str(), s) == 0) {
				return TRUE;
			}
		}
	}
	return FALSE;
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
	try {
		PlCall("retractall(event(_))");
		
		// simple values
		PlCall("assert", PlCompound("event", PlCompound("name", PlTerm(event.name.c_str()))));
		PlCall("assert", PlCompound("event", PlCompound("origin", PlString(event.origin.c_str()))));
		PlCall("assert", PlCompound("event", PlCompound("origintype", PlString(event.invokeid.c_str()))));
		PlCall("assert", PlCompound("event", PlCompound("invokeid", PlTerm(event.origintype.c_str()))));
		PlCall("assert", PlCompound("event", PlCompound("raw", PlString(event.raw.c_str()))));

		// event.type
		std::string type;
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
		PlCall("assert", PlCompound("event", PlCompound("type", PlTerm(type.c_str()))));
		
		// event.sendid
		if (!event.hideSendId)
			PlCall("assert", PlCompound("event", PlCompound("sendid", PlTerm(event.sendid.c_str()))));
		
		// event.data
		URL domUrl;
		if (event.dom) {
			std::stringstream dataInitStr;
			std::stringstream xmlDoc;
			xmlDoc << event.getFirstDOMElement();
			domUrl = URL::toLocalFile(xmlDoc.str(), ".pl");
			dataInitStr << "load_xml_file('" << domUrl.asLocalFile(".pl") << "', XML), copy_term(XML,DATA), assert(event(data(DATA)))";
			PlCall(dataInitStr.str().c_str());
		} else if (event.content.size() > 0) {
			PlCall("assert", PlCompound("event", PlCompound("data", PlString(Interpreter::spaceNormalize(event.content).c_str()))));
		}	
		
		// event.params
		size_t uniqueKeys = 0;
		Event::params_t::const_iterator paramIter = event.params.begin();
		while(paramIter != event.params.end()) {
			uniqueKeys++;
			paramIter = event.params.upper_bound(paramIter->first);
		}
		if (uniqueKeys > 0) {
			paramIter = event.params.begin();
			for(int i = 0; paramIter != event.params.end(); i++) {
				std::stringstream paramArray;
				Event::params_t::const_iterator	lastValueIter = event.params.upper_bound(paramIter->first);

				paramArray << paramIter->first << "([";
				std::string termSep = "";

				for (int j = 0; paramIter != lastValueIter; j++) {
					paramArray << termSep << "'" << paramIter->second << "'";
					termSep = ", ";
					paramIter++;
				}
				paramArray << "])";
				std::stringstream paramExpr;
				paramExpr << "assert(event(param(" << paramArray.str() << ")))";
				//std::cout << paramExpr.str() << std::endl;
				PlCall(paramExpr.str().c_str());
				
				paramIter = lastValueIter;
			}
		}
	} catch(PlException e) {
		LOG(ERROR) << e.operator const char *();
	}
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
	PlCompound compound(expr.c_str());
	PlTermv termv(compound.arity());
	for (int i = 0; i < compound.arity(); i++) {
		termv[i] = compound[i + 1];
	}
	PlQuery query(compound.name(), termv);
	uint32_t length = 0;
	while(query.next_solution() > 0)
		length++;
	return length;
}

void SWIDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
	PlCompound compound(array.c_str());
	PlCompound orig(array.c_str());
	PlTermv termv(compound.arity());
	for (int i = 0; i < compound.arity(); i++) {
		termv[i] = compound[i + 1];
	}
	{
		int tmp = iteration + 1;
		PlQuery query(compound.name(), termv);
		while (tmp) {
			query.next_solution();
			tmp--;
		}
	}
	PlCall("retractall", PlCompound(index.c_str(), 1));
	PlCall("retractall", PlCompound(item.c_str(), 1));
	PlCall("assert", PlCompound(index.c_str(), PlTerm((long)iteration)));
	
	std::map<std::string, PlTerm> vars = resolveAtoms(compound, orig);
	std::map<std::string, PlTerm>::iterator varIter = vars.begin();
	while(varIter != vars.end()) {
		PlCall("assert", PlCompound(item.c_str(), varIter->second));
		varIter++;
	}
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
	PlCompound orig(expr.c_str()); // keep the original to find variables
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
			std::map<std::string, PlTerm> vars = resolveAtoms(compound, orig);
			if (vars.size() == 1) {
				ss << (char *)vars.begin()->second;
			} else {
				std::map<std::string, PlTerm>::const_iterator varIter = vars.begin();
				while(varIter != vars.end()) {
					ss << separator << (char *)varIter->second;
					separator = ", ";
					varIter++;
				}
			}
		}
		return ss.str();
	}
	return std::string(compound);
}

// this is similar to http://etalis.googlecode.com/svn/eEtalis/src/term.c
std::map<std::string, PlTerm> SWIDataModel::resolveAtoms(PlTerm& term, PlTerm& orig) {
	std::map<std::string, PlTerm> atoms;
	switch (orig.type()) {
		case PL_VARIABLE: {
			atoms[(char *)orig] = term;
			break;
		}
		case PL_ATOM:
			break;
		case PL_STRING:
			break;
		case PL_INTEGER:
			break;
		case PL_TERM:
			for (int i = 1; i <= orig.arity(); i++) {
				PlTerm newTerm = term[i];
				PlTerm newOrig = orig[i];
				std::map<std::string, PlTerm> result = resolveAtoms(newTerm, newOrig);
				atoms.insert(result.begin(), result.end());
			}
			break;
	}
	return atoms;
}
	
void SWIDataModel::assign(const Arabica::DOM::Element<std::string>& assignElem,
                          const Arabica::DOM::Document<std::string>& doc,
                          const std::string& content) {
	std::string expr = content;
	std::string predicate;
	if (HAS_ATTR(assignElem, "expr")) {
		expr = ATTR(assignElem, "expr");
	}
	if (HAS_ATTR(assignElem, "id"))
		predicate = ATTR(assignElem, "id");
	if (HAS_ATTR(assignElem, "location"))
		predicate = ATTR(assignElem, "location");

	if (predicate.size() > 0) {
		size_t aritySep = predicate.find_first_of("/");
		if (aritySep != std::string::npos) {
			std::string functor = predicate.substr(0, aritySep);
			std::string arity = predicate.substr(aritySep + 1);
			std::string callAssert = "assert";
			if (HAS_ATTR(assignElem, "type")) {
				std::string type = ATTR(assignElem, "type");
				if (boost::iequals(type, "retract")) {
					PlCall("retractall", PlCompound(functor.c_str(), strTo<long>(arity)));
				} else if(boost::iequals(type, "append")) {
					callAssert = "assertz";
				} else if(boost::iequals(type, "prepend")) {
					callAssert = "asserta";
				}
			}
			// treat content as . seperated facts
			std::stringstream factStream(content);
			std::string item;
			while(std::getline(factStream, item, '.')) {
				std::string fact = boost::trim_copy(item);
				if (fact.length() == 0)
					continue;
				PlCall((callAssert + "(" + functor + "(" + fact + "))").c_str());
			}
			
		}
	} else if (expr.length() > 0) {
		eval(expr);
	}
}

void SWIDataModel::assign(const std::string& location, const Data& data) {
	eval(data.atom);
}

void SWIDataModel::init(const Arabica::DOM::Element<std::string>& dataElem,
                        const Arabica::DOM::Document<std::string>& doc,
                        const std::string& content) {
	assign(dataElem, doc, content);
}
void SWIDataModel::init(const std::string& location, const Data& data) {
	assign(location, data);
}

bool SWIDataModel::isDeclared(const std::string& expr) {
	return true;
}

}
