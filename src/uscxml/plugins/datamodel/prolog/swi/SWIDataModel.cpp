/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include <boost/algorithm/string.hpp>

#include "uscxml/Common.h"
#include "uscxml/config.h"
#include "SWIDataModel.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

// these are defined but not exported by swi-prolog 7
extern "C" {
	PL_EXPORT(int) PL_is_dict(term_t t);
	PL_EXPORT(int) PL_for_dict(term_t dict, int (*func)(term_t key, term_t value, int last, void *closure), void *closure, int flags);
}
#define RETHROW_PLEX_AS_EVENT \
catch (PlException plex) { \
	Event e; \
	e.name = "error.execution"; \
	e.data.compound["cause"] = (char*)plex; \
	throw e; \
} \

// this might evolve into multi-threaded prolog, but no need for now
#define SET_PL_CONTEXT \
_dmPtr = this;

#define PL_MODULE \
_interpreter.getSessionId().c_str() \
 
#define UNSET_PL_ENGINE(dm) \
PL_set_engine(NULL, NULL);

#define SET_PL_ENGINE(dm) \
assert(_swiEngines.find(dm) != _swiEngines.end()); \
int rc = PL_set_engine(_swiEngines[dm], NULL); \
assert(rc == PL_ENGINE_SET); \
_dmPtr = dm;

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new SWIDataModelProvider() );
	return true;
}
#endif

// SWI prolog does not support passing user data
static SWIDataModel* _dmPtr;
static std::map<SWIDataModel*, PL_engine_t> _swiEngines;

PL_blob_t SWIDataModel::blobType =
{ PL_BLOB_MAGIC,
	PL_BLOB_NOCOPY,
	"blob",
	releaseBlob,
	compareBlob,
	writeBlob,
	acquireBlob
};

SWIDataModel::SWIDataModel() {
}

SWIDataModel::~SWIDataModel() {
	try {
		if (_swiEngines.find(this) != _swiEngines.end()) {
			PL_destroy_engine(_swiEngines[this]);
			_swiEngines.erase(this);
		}
	} RETHROW_PLEX_AS_EVENT;
}

boost::shared_ptr<DataModelImpl> SWIDataModel::create(InterpreterImpl* interpreter) {
	try {
		boost::shared_ptr<SWIDataModel> dm = boost::shared_ptr<SWIDataModel>(new SWIDataModel());
		dm->_interpreter = interpreter;

		const char* swibin = getenv("SWI_BINARY");
		if (swibin == NULL)
			swibin = SWI_BINARY;
		const char* quiet = "--quiet";

		int argc = 2;
		static char * av[] = {
			(char*)swibin,
			(char*)quiet,
			NULL
		};

		PL_engine_t engine;

		if (!PL_is_initialised(NULL, NULL)) {
			if(!PL_initialise(argc,av)) {
				LOG(ERROR) << "Error intializing prolog engine";
				PL_halt(1);
				return boost::shared_ptr<DataModelImpl>();
			}

			PL_set_engine(PL_ENGINE_CURRENT, &engine);

			// load SWI XML parser
			try {
				PlCall("use_module", PlCompound("library", PlTerm("sgml")));
			} catch (PlException plex) {

				LOG(ERROR) << "Cannot load prolog sgml module - make sure you have it installed in your prolog runtime: " << (char*)plex;
				throw plex;
			}

			// load json parser
			try {
				PlCall("use_module", PlCompound("library", PlTerm("http/json")));
				PlCall("use_module", PlCompound("library", PlTerm("http/json_convert")));
			} catch (PlException plex) {
				LOG(ERROR) << "Cannot load prolog json module or json_convert - make sure you have it installed in your prolog runtime: " << (char*)plex;
				throw plex;
			}

		} else {
			LOG(WARNING) << "Instantiating more than one SWI prolog datamodel will lead to weird effects as I cannot seperate the environments";
			engine = PL_create_engine(NULL);
		}

		assert(engine);
		_swiEngines[dm.get()] = engine;
		_dmPtr = dm.get();

		int rc = PL_set_engine(engine, NULL);
		assert(rc == PL_ENGINE_SET);
		(void)rc;

		_plModule = boost::replace_all_copy(interpreter->getSessionId(), "-", "");
		boost::replace_all(_plModule, "0", "g");
		boost::replace_all(_plModule, "1", "h");
		boost::replace_all(_plModule, "2", "i");
		boost::replace_all(_plModule, "3", "j");
		boost::replace_all(_plModule, "4", "k");
		boost::replace_all(_plModule, "5", "l");
		boost::replace_all(_plModule, "6", "m");
		boost::replace_all(_plModule, "7", "n");
		boost::replace_all(_plModule, "8", "o");
		boost::replace_all(_plModule, "9", "p");

		// use atoms for double quoted
		PlCall("set_prolog_flag(double_quotes,atom).");

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
	} RETHROW_PLEX_AS_EVENT;
}

foreign_t SWIDataModel::inPredicate(term_t a0, int arity, void* context) {
	try {
		char *s;
		if ( PL_get_atom_chars(a0, &s) ) {
			NodeSet<std::string> config = _dmPtr->_interpreter->getConfiguration();
			for (int i = 0; i < config.size(); i++) {
				if (HAS_ATTR(config[i], "id") && strcmp(ATTR(config[i], "id").c_str(), s) == 0) {
					return TRUE;
				}
			}
		}
		return FALSE;
	} RETHROW_PLEX_AS_EVENT;
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

	SET_PL_CONTEXT;
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
		switch (event.eventType) {
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
//			xmlDoc << event.getFirstDOMElement();
			xmlDoc << event.dom;
			domUrl = URL::toLocalFile(xmlDoc.str(), ".pl");
			dataInitStr << "load_xml_file('" << domUrl.asLocalFile(".pl") << "', XML), copy_term(XML,DATA), assert(event(data(DATA)))";
			PlCall(dataInitStr.str().c_str());
		} else if (event.content.size() > 0) {
			PlCall("assert", PlCompound("event", PlCompound("data", PlString(Interpreter::spaceNormalize(event.content).c_str()))));
		} else if (event.data) {
			assertFromData(event.data, "event(data(", 2);
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
	} RETHROW_PLEX_AS_EVENT;
}

void SWIDataModel::assertFromData(const Data& data, const std::string& expr, size_t nesting) {
	if (data.atom.size() > 0) {
		std::stringstream ss;
		ss << expr << "(";
		nesting++;

		if (data.type == Data::VERBATIM) {
			ss << "\"" << data.atom << "\"";
		} else {
			ss << data.atom;
		}
		
		for (size_t i = 0; i < nesting; i++) {
			ss << ")";
		}
		PlCall("assert", PlCompound(ss.str().c_str()));
		return;
	}
	
	if (data.compound.size() > 0) {
		std::map<std::string, Data>::const_iterator compIter = data.compound.begin();
		while(compIter != data.compound.end()) {
			assertFromData(compIter->second, expr + "(" + compIter->first, nesting + 1);
			compIter++;
		}
	}
	
	if (data.array.size() > 0) {
		std::list<Data>::const_iterator arrIter = data.array.begin();
		while(arrIter != data.array.end()) {
			assertFromData(*arrIter, expr, nesting);
			arrIter++;
		}
	}
	
	if (data.node) {
		std::stringstream dataInitStr;
		std::stringstream xmlDoc;

		xmlDoc << data.node;
		URL domUrl = URL::toLocalFile(xmlDoc.str(), ".pl");
		dataInitStr << "load_xml_file('" << domUrl.asLocalFile(".pl") << "', XML), ";
		dataInitStr << "copy_term(XML,DATA), ";
		dataInitStr << "assert(";
		dataInitStr << expr << "(DATA)";
		
		for (size_t i = 0; i < nesting; i++) {
			dataInitStr << ")";
		}

		PlCall(dataInitStr.str().c_str());
		return;
	}
}

Data SWIDataModel::getStringAsData(const std::string& content) {
	SET_PL_CONTEXT
	try {
		PlTerm term(content.c_str());
		return(termAsData(term));
	} RETHROW_PLEX_AS_EVENT
}

Data SWIDataModel::termAsData(PlTerm term) {
	Data data;

//	std::cout << term.name() << (char*)term << std::endl;
	
	switch (term.type()) {
		case PL_TERM:
			for (int i = 1; i <= term.arity(); i++) { // arguments start at 1
				data.compound[term.name()].array.push_back(termAsData(term[i]));
			}
			break;
		case PL_INTEGER:
		case PL_FLOAT:
		case PL_SHORT:
		case PL_INT:
		case PL_LONG:
		case PL_DOUBLE:
			data.atom = std::string(term);
			data.type = Data::INTERPRETED;
			break;
		case PL_ATOM:
			data.atom = std::string(term);
			data.type = Data::VERBATIM;
			break;
		case PL_NIL:
			data.array.push_back(Data("", Data::VERBATIM));
			break;
		case PL_LIST_PAIR: {
			PlTail tail(term);
			PlTerm item;
			while(tail.next(item)) {
				data.array.push_back(termAsData(item));
			}
			break;
		}
		case PL_DICT: {
			std::string key(term);
			size_t curlyPos = key.find_first_of("{");
			if (curlyPos == std::string::npos || curlyPos == 0) {
				// no key given
				PL_for_dict(term, SWIDataModel::dictCallBack, &data, 0);
			} else {
				// with key given
				Data& tmp = data.compound[boost::trim_copy(key.substr(0, curlyPos))];
				PL_for_dict(term, SWIDataModel::dictCallBack, &tmp, 0);
			}
			break;
		}
		default:
			LOG(ERROR) << "Prolog type " << term.type() << " at '" << (char*)term << "' not supported";
			break;
	}
	return data;
}

int SWIDataModel::dictCallBack(term_t key, term_t value, int last, void *closure) {
	Data* data = (Data*)closure;
	PlTerm keyTerm(key);
	data->compound[(char*)keyTerm] = termAsData(value);
	return 0;
}

PlTerm SWIDataModel::dataAsTerm(Data data) {
	if (data.atom.length() > 0) {
		return PlTerm(data.atom.c_str());
	}
	if (data.array.size() > 0) {
		PlTerm head;
		PlTail list(head);
		
		std::list<Data>::const_iterator arrIter = data.array.begin();
		while(arrIter != data.array.end()) {
			list.append(dataAsTerm(*arrIter));
			arrIter++;
		}
		list.close();
		return PlTail(head);
	}
	if (data.compound.size() > 0) {
		if (data.compound.size() == 1 && data.compound.begin()->second.array.size() > 0) {
			// this used to be a prolog compound
			const Data& arr = data.compound.begin()->second;
			PlTermv termv(arr.array.size());
			int index = 0;

			std::list<Data>::const_iterator arrIter = arr.array.begin();
			while(arrIter != arr.array.end()) {
				termv[index] = dataAsTerm(*arrIter);
				index++;
				arrIter++;
			}
			return PlCompound(data.compound.begin()->first.c_str(), termv);
		} else if (data.compound.size() == 1 && data.compound.begin()->second.compound.size() > 0) {
			// this used to be a named dict - until we have dict support in C/C++ use PL_chars_to_term
			std::stringstream dictSS;
			std::string seperator;
			dictSS << data.compound.begin()->first << "{";
			
			std::map<std::string, Data>::const_iterator keyIter = data.compound.begin()->second.compound.begin();
			while(keyIter != data.compound.begin()->second.compound.end()) {
				dictSS << seperator << keyIter->first << ":" << (char*)dataAsTerm(keyIter->second);
				seperator = ",";
				keyIter++;
			}
			dictSS << "}";
			return PlCompound(dictSS.str().c_str());
			
		} else {
			// an array of dicts
			PlTermv termv(data.compound.size());
			int index = 0;
			
			std::map<std::string, Data>::const_iterator compIter = data.compound.begin();
			while(compIter != data.compound.end()) {
				termv[index] = PlCompound(compIter->first.c_str(), dataAsTerm(compIter->second));
				index++;
				compIter++;
			}
			return PlCompound(data.compound.begin()->first.c_str(), termv);

		}
	}
	if (data.binary) {
		LOG(ERROR) << "Binary data with prolog datamodel still very experimental";
//		term_t binTerm = PL_new_term_ref();
//		PL_put_blob(binTerm, data.binary->data, data.binary->size, &blobType);
//		return binTerm;
	}
	if (data.node) {
		LOG(ERROR) << "DOM in event with prolog datamodel still very experimental";
		std::stringstream dataInitStr;
		std::stringstream xmlDoc;
		//			xmlDoc << event.getFirstDOMElement();
		xmlDoc << data.node;
		URL domUrl = URL::toLocalFile(xmlDoc.str(), ".pl");
		dataInitStr << "load_xml_file('" << domUrl.asLocalFile(".pl") << "', XML), copy_term(XML,DATA), assert(event(data(DATA)))";
		PlCall(dataInitStr.str().c_str());
	}
	
	return PlTerm();
}

bool SWIDataModel::validate(const std::string& location, const std::string& schema) {
	SET_PL_CONTEXT
//	std::cout << "SWIDataModel::validate" << std::endl;
	return true;
}

uint32_t SWIDataModel::getLength(const std::string& expr) {
	SET_PL_CONTEXT
	try {
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
	} RETHROW_PLEX_AS_EVENT;
}

void SWIDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
	SET_PL_CONTEXT
	try {
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
	} RETHROW_PLEX_AS_EVENT;
}

void SWIDataModel::eval(const Element<std::string>& scriptElem, const std::string& expr) {
	SET_PL_CONTEXT
	try {
		if (scriptElem && HAS_ATTR(scriptElem, "type") && iequals(ATTR(scriptElem, "type"), "query")) {
			evalAsBool(expr);
		} else {
			URL localPLFile = URL::toLocalFile(expr, ".pl");
			PlCall("user", "load_files", PlTermv(localPLFile.asLocalFile(".pl").c_str())) || LOG(ERROR) << "Could not execute prolog from file";
		}
	} RETHROW_PLEX_AS_EVENT;
}

bool SWIDataModel::evalAsBool(const std::string& expr) {
	return evalAsBool(Arabica::DOM::Node<std::string>(), expr);
}

bool SWIDataModel::evalAsBool(const Arabica::DOM::Node<std::string>& node, const std::string& expr) {
	SET_PL_CONTEXT
	try {
		PlCompound compound(expr.c_str());
		PlTermv termv(compound.arity());
		for (int i = 0; i < compound.arity(); i++) {
			termv[i] = compound[i + 1];
		}
		PlQuery query(compound.name(), termv);
		return query.next_solution() > 0;
	} catch(...) {
		return false;
	}
}

std::string SWIDataModel::evalAsString(const std::string& expr) {
	SET_PL_CONTEXT
	try {
		
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
					ss << separator << (char *)vars.begin()->second;
					separator = "\n";
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

	} catch(PlException plex) {
		// we got an exception while trying to evaluate as compound
		PlTerm term(expr.c_str());
		if (term.type() == PL_ATOM | term.type() == PL_CHARS | term.type() == PL_STRING) {
			return std::string(term);
		} else {
			Event e;
			e.name = "error.execution";
			e.data.compound["cause"] = (char*)plex;
			throw e;
		}
	}
}

// this is similar to http://etalis.googlecode.com/svn/eEtalis/src/term.c
std::map<std::string, PlTerm> SWIDataModel::resolveAtoms(PlTerm& term, PlTerm& orig) {
	SET_PL_CONTEXT
	try {
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
	} RETHROW_PLEX_AS_EVENT
}

void SWIDataModel::assign(const Element<std::string>& assignElem,
                          const Node<std::string>& node,
                          const std::string& content) {
	SET_PL_CONTEXT
	try {
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
			std::string callAssert = "assert";
			std::string type;
			if (HAS_ATTR(assignElem, "type")) {
				type = ATTR(assignElem, "type");
				if(iequals(type, "append")) {
					callAssert = "assertz";
				} else if(iequals(type, "prepend")) {
					callAssert = "asserta";
				}
			}

			URL domUrl;
			Data json;
			if (!node)
				json = Data::fromJSON(expr);
			if (node) {
				std::stringstream dataInitStr;
				std::stringstream xmlDoc;
				Node<std::string> child = node;
				while(child) {
					xmlDoc << child;
					child = child.getNextSibling();
				}
				domUrl = URL::toLocalFile(xmlDoc.str(), ".pl");
				if (iequals(type, "retract"))
					PlCall("retractall", PlCompound(predicate.c_str(), 1));
				dataInitStr << "load_xml_file('" << domUrl.asLocalFile(".pl") << "', XML), copy_term(XML,DATA), " << callAssert << "(" << predicate << "(DATA))";
				PlCall(dataInitStr.str().c_str());
			} else if (json) {
				std::stringstream dataInitStr;
				if (iequals(type, "retract"))
					PlCall("retractall", PlCompound(predicate.c_str(), 1));
				dataInitStr << "json_to_prolog(" << expr << ", JSON), assert(" << predicate << "(JSON))";
				PlCall(dataInitStr.str().c_str());
			} else {
				// treat content as . seperated facts
				std::stringstream factStream(content);
				std::string item;
				while(std::getline(factStream, item, '.')) {
					std::string fact = boost::trim_copy(item);
					if (fact.length() == 0)
						continue;
					PlCall((callAssert + "(" + predicate + "(" + fact + "))").c_str());
				}
			}
		} else if (expr.length() > 0) {
			if (boost::equals(TAGNAME(assignElem), "data")) {
				eval(assignElem, expr);
			} else {
				std::stringstream exprStream(expr);
				std::string item;
				while(std::getline(exprStream, item, '.')) {
					std::string plExpr = boost::trim_copy(item);
					if (plExpr.length() == 0)
						continue;
					PlCall(plExpr.c_str());
				}
			}
		}
	} RETHROW_PLEX_AS_EVENT
}

void SWIDataModel::assign(const std::string& location, const Data& data) {
	eval(Element<std::string>(), data.atom);
}

void SWIDataModel::init(const Element<std::string>& dataElem,
                        const Node<std::string>& node,
                        const std::string& content) {
	assign(dataElem, node, content);
}
void SWIDataModel::init(const std::string& location, const Data& data) {
	assign(location, data);
}

bool SWIDataModel::isDeclared(const std::string& expr) {
	return true;
}

void SWIDataModel::acquireBlob(atom_t symbol) {
}
	
	
int SWIDataModel::releaseBlob(atom_t symbol) {
	return TRUE;
}

int SWIDataModel::compareBlob(atom_t a, atom_t b) {
	return 0;
}

int SWIDataModel::writeBlob(void *s, atom_t symbol, int flags) {
	return TRUE;
}

	
}
