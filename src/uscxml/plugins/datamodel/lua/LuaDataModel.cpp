/**
 *  @file
 *  @author     2012-2014 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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
#include "LuaDataModel.h"

#include "LuaBridge.h"
//#include "RefCountedPtr.h"

#include "uscxml/DOMUtils.h"

#include "uscxml/Message.h"
#include <glog/logging.h>

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new LuaDataModelProvider() );
	return true;
}
#endif

static int luaInspect(lua_State * l) {
	return 0;
}

static luabridge::LuaRef getDataAsLua(lua_State* _luaState, const Data& data) {
	luabridge::LuaRef luaData (_luaState);

	if (data.node) {
		ERROR_EXECUTION_THROW("No DOM support in Lua datamodel");
	}
	if (data.compound.size() > 0) {
		luaData = luabridge::newTable(_luaState);
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			luaData[compoundIter->first] = getDataAsLua(_luaState, compoundIter->second);
			compoundIter++;
		}
		luaData["inspect"] = luaInspect;
		return luaData;
	}
	if (data.array.size() > 0) {
		luaData = luabridge::newTable(_luaState);
		std::list<Data>::const_iterator arrayIter = data.array.begin();
		uint32_t index = 0;
		while(arrayIter != data.array.end()) {
			luaData[index++] = getDataAsLua(_luaState, *arrayIter);
			arrayIter++;
		}
		luaData["inspect"] = luaInspect;
		return luaData;
	}
	if (data.atom.size() > 0) {
		switch (data.type) {
		case Data::VERBATIM: {
//				luaData = "\"" + data.atom + "\"";
			luaData = data.atom;
			break;
		}
		case Data::INTERPRETED: {
			if (isNumeric(data.atom.c_str(), 10)) {
				if (data.atom.find(".") != std::string::npos) {
					luaData = strTo<double>(data.atom);
				} else {
					luaData = strTo<long>(data.atom);
				}
			} else {
				luaData = data.atom;
			}
		}
		}
		return luaData;
	}
	return luaData;
}

LuaDataModel::LuaDataModel() {
	_luaState = NULL;
}

static int luaInFunction(lua_State * l) {
	luabridge::LuaRef ref = luabridge::getGlobal(l, "__interpreter");
	InterpreterImpl* interpreter = ref.cast<InterpreterImpl*>();

	int stackSize = lua_gettop(l);
	for (int i = 0; i < stackSize; i++) {
		if (!lua_isstring(l, -1 - i))
			continue;
		std::string stateName = lua_tostring(l, -1 - i);
		if (interpreter->isInState(stateName))
			continue;
		lua_pushboolean(l, 0);
		return 1;
	}
	lua_pushboolean(l, 1);
	return 1;
}


boost::shared_ptr<DataModelImpl> LuaDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<LuaDataModel> dm = boost::shared_ptr<LuaDataModel>(new LuaDataModel());
	dm->_interpreter = interpreter;
	dm->_luaState = luaL_newstate();
	luaL_openlibs(dm->_luaState);

	luabridge::getGlobalNamespace(dm->_luaState).beginClass<InterpreterImpl>("Interpreter").endClass();
	luabridge::setGlobal(dm->_luaState, dm->_interpreter, "__interpreter");

	luabridge::getGlobalNamespace(dm->_luaState).addCFunction("In", luaInFunction);

	luabridge::LuaRef ioProcTable = luabridge::newTable(dm->_luaState);

	std::map<std::string, IOProcessor>::const_iterator ioProcIter = dm->_interpreter->getIOProcessors().begin();
	while(ioProcIter != dm->_interpreter->getIOProcessors().end()) {
		Data ioProcData = ioProcIter->second.getDataModelVariables();
		ioProcTable[ioProcIter->first] = getDataAsLua(dm->_luaState, ioProcData);
		ioProcIter++;
	}
	luabridge::setGlobal(dm->_luaState, ioProcTable, "_ioprocessors");

	luabridge::setGlobal(dm->_luaState, dm->_interpreter->getName(), "_name");
	luabridge::setGlobal(dm->_luaState, dm->_interpreter->getSessionId(), "_sessionid");

	return dm;
}

LuaDataModel::~LuaDataModel() {
	if (_luaState != NULL)
		lua_close(_luaState);
}

void LuaDataModel::pushContext() {
}

void LuaDataModel::popContext() {
}

void LuaDataModel::initialize() {
}

static Data getLuaAsData(const luabridge::LuaRef& lua) {
	Data data;
	if (lua.isFunction()) {
		// TODO: this might lead to a stack-overflow
		luabridge::LuaRef luaEvald = lua();
		return getLuaAsData(luaEvald);
	} else if(lua.isLightUserdata() || lua.isUserdata()) {
		// not sure what to do
	} else if(lua.isThread()) {
		// not sure what to do
	} else if(lua.isNil()) {
		data.atom = "undefined";
		data.type = Data::INTERPRETED;
	} else if(lua.isString()) {
		data.atom = lua.tostring();
		data.type = Data::VERBATIM;
	} else if(lua.isNumber()) {
		data.atom = lua.tostring();
		data.type = Data::INTERPRETED;
	} else if(lua.isTable()) {
		for (luabridge::Iterator iter (lua); !iter.isNil (); ++iter) {
			luabridge::LuaRef luaKey = iter.key();
			luabridge::LuaRef luaVal = *iter;
			data.compound[luaKey.tostring()] = getLuaAsData(luaVal);
		}
	}
	return data;
}

void LuaDataModel::setEvent(const Event& event) {
	luabridge::LuaRef luaEvent(_luaState);
	luaEvent = luabridge::newTable(_luaState);

	luaEvent["name"] = event.name;
	luaEvent["raw"] = event.raw;
	luaEvent["xml"] = event.xml;
	luaEvent["origin"] = event.origin;
	luaEvent["origintype"] = event.origintype;
	luaEvent["content"] = event.content;
	luaEvent["invokeId"] = event.invokeid;
	luaEvent["sendId"] = event.sendid;
	luaEvent["inspect"] = luaInspect;

	switch (event.eventType) {
	case Event::INTERNAL:
		luaEvent["type"] = "internal";
		break;
	case Event::EXTERNAL:
		luaEvent["type"] = "external";
		break;
	case Event::PLATFORM:
		luaEvent["type"] = "platform";
		break;

	default:
		break;
	}

	if (event.dom) {
		ERROR_EXECUTION_THROW("No DOM support in Lua datamodel");
	} else if (event.content.length() > 0) {
		// _event.data is a string or JSON
		Data json = Data::fromJSON(event.content);
		if (!json.empty()) {
			luaEvent["data"] = getDataAsLua(_luaState, json);
		} else {
			// test179
			std::string trimmed = boost::trim_copy(event.content);
			if ((boost::starts_with(trimmed, "'") && boost::ends_with(trimmed, "'")) ||
			        (boost::starts_with(trimmed, "\"") && boost::ends_with(trimmed, "\""))) {
				luaEvent["data"] = InterpreterImpl::spaceNormalize(event.content);
			} else {
				Data tmp(event.content, Data::INTERPRETED);
				luaEvent["data"] = getDataAsLua(_luaState, tmp);
			}
		}
	} else {
		// _event.data is KVP
		Event eventCopy(event);

		if (!eventCopy.params.empty()) {
			Event::params_t::iterator paramIter = eventCopy.params.begin();
			while(paramIter != eventCopy.params.end()) {
				eventCopy.data.compound[paramIter->first] = paramIter->second;
				paramIter++;
			}
		}
		if (!eventCopy.namelist.empty()) {
			Event::namelist_t::iterator nameListIter = eventCopy.namelist.begin();
			while(nameListIter != eventCopy.namelist.end()) {
				eventCopy.data.compound[nameListIter->first] = nameListIter->second;
				nameListIter++;
			}
		}

		if (!eventCopy.data.empty()) {
			luabridge::LuaRef luaData = getDataAsLua(_luaState, eventCopy.data);
			assert(luaEvent.isTable());
			assert(luaData.isTable());
			luaEvent["data"] = luaData;
		}
	}

	luabridge::setGlobal(_luaState, luaEvent, "_event");
}

Data LuaDataModel::getStringAsData(const std::string& content) {
	Data data = Data::fromJSON(content);
	if (data.empty()) {
		std::string trimmedExpr = boost::trim_copy(content);
		if (!boost::starts_with(trimmedExpr, "return")) {
			trimmedExpr = "return(" + trimmedExpr + ");";
		}

		int retVals = luaEval(Arabica::DOM::Element<std::string>(), trimmedExpr);
		if (retVals == 1) {
			data = getLuaAsData(luabridge::LuaRef::fromStack(_luaState, -1));
		}
		lua_pop(_luaState, retVals);

	}
	return data;
}

bool LuaDataModel::validate(const std::string& location, const std::string& schema) {
	return true;
}

bool LuaDataModel::isLocation(const std::string& expr) {
	return true;
}

uint32_t LuaDataModel::getLength(const std::string& expr) {
	// we need the result of the expression on the lua stack -> has to "return"!
	std::string trimmedExpr = boost::trim_copy(expr);

	if (!boost::starts_with(trimmedExpr, "return")) {
		trimmedExpr = "return(#" + trimmedExpr + ")";
	}

	int retVals = luaEval(Arabica::DOM::Element<std::string>(), trimmedExpr);

	if (retVals == 1 && lua_isnumber(_luaState, -1)) {
		int result = lua_tointeger(_luaState, -1);
		lua_pop(_luaState, 1);
		return result;
	}

	lua_pop(_luaState, retVals);
	ERROR_EXECUTION_THROW("'" + expr + "' does not evaluate to an array.");
	return 0;
}

void LuaDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
	iteration++; // test153: arrays start at 1

	const luabridge::LuaRef& arrRef = luabridge::getGlobal(_luaState, array.c_str());
	if (arrRef.isTable()) {

		// trigger syntax error for invalid items
		int retVals = luaEval(Arabica::DOM::Element<std::string>(), "return(" + item + ");");
		lua_pop(_luaState, retVals);

		const luabridge::LuaRef& val = arrRef[iteration];
		luabridge::setGlobal(_luaState, val, item.c_str());

		if (index.length() > 0) {
			// assign iteration element to index
			luabridge::setGlobal(_luaState, iteration, index.c_str());
		}
	}
}

void LuaDataModel::eval(const Arabica::DOM::Element<std::string>& scriptElem,
                        const std::string& expr) {
	luaEval(scriptElem, expr);
}

int LuaDataModel::luaEval(const Arabica::DOM::Element<std::string>& scriptElem,
                          const std::string& expr) {
	int preStack = lua_gettop(_luaState);
	int error = luaL_loadstring(_luaState, expr.c_str()) || lua_pcall(_luaState, 0, LUA_MULTRET, 0);
	if (error) {
		std::string errMsg = lua_tostring(_luaState, -1);
		lua_pop(_luaState, 1);  /* pop error message from the stack */
		ERROR_EXECUTION_THROW(errMsg);
	}
	int postStack = lua_gettop(_luaState);
	return postStack - preStack;
}

bool LuaDataModel::isDeclared(const std::string& expr) {
	// see: http://lua-users.org/wiki/DetectingUndefinedVariables
	return true;
}

void LuaDataModel::assign(const Arabica::DOM::Element<std::string>& assignElem,
                          const Arabica::DOM::Node<std::string>& node,
                          const std::string& content) {
	std::string key;
	if (HAS_ATTR(assignElem, "id")) {
		key = ATTR(assignElem, "id");
	} else if (HAS_ATTR(assignElem, "location")) {
		key = ATTR(assignElem, "location");
	}
	if (key.length() == 0) {
		ERROR_EXECUTION_THROW("Assign element has neither id nor location");
	}

	// flags on attribute are ignored?
	if (key.compare("_sessionid") == 0) // test 322
		ERROR_EXECUTION_THROW("Cannot assign to _sessionId");
	if (key.compare("_name") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _name");
	if (key.compare("_ioprocessors") == 0)  // test 326
		ERROR_EXECUTION_THROW("Cannot assign to _ioprocessors");
	if (key.compare("_invokers") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _invokers");
	if (key.compare("_event") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _event");

//	lua_pushnil(_luaState);
//	lua_setglobal(_luaState, key.c_str());

//	luabridge::setGlobal(_luaState, luabridge::Nil(), key.c_str());
//	luabridge::LuaRef val = luabridge::getGlobal(_luaState, key.c_str());
//	std::cout << val.tostring() << std::endl;

	int retVals = 0;

	if (HAS_ATTR(assignElem, "expr")) {
		retVals = luaEval(Arabica::DOM::Element<std::string>(), key + " = " + ATTR(assignElem, "expr") + ";");
	} else if (node) {
		ERROR_EXECUTION_THROW("Cannot assign xml nodes in lua datamodel");
	} else if (content.size() > 0) {
		try {
			eval(Arabica::DOM::Element<std::string>(), key + " = " + content + ";");
		} catch (...) {
			eval(Arabica::DOM::Element<std::string>(), key + " = " + "\"" + InterpreterImpl::spaceNormalize(content) + "\";");
		}
	} else {
		eval(Arabica::DOM::Element<std::string>(), key + " = " + "nil;");
	}

//	val = luabridge::getGlobal(_luaState, key.c_str());
//	std::cout << val.tostring() << std::endl;

}

void LuaDataModel::assign(const std::string& location, const Data& data) {
	luabridge::setGlobal(_luaState, getDataAsLua(_luaState, data), location.c_str());
}

void LuaDataModel::init(const Arabica::DOM::Element<std::string>& dataElem,
                        const Arabica::DOM::Node<std::string>& node,
                        const std::string& content) {
	assign(dataElem, node, content);
}

void LuaDataModel::init(const std::string& location, const Data& data) {
	assign(location, data);
}

/**
 * The boolean expression language consists of the In predicate only. It has the
 * form 'In(id)', where id is the id of a state in the enclosing state machine.
 * The predicate must return 'true' if and only if that state is in the current
 * state configuration.
 */
bool LuaDataModel::evalAsBool(const Arabica::DOM::Element<std::string>& node, const std::string& expr) {
	// we need the result of the expression on the lua stack -> has to "return"!
	std::string trimmedExpr = boost::trim_copy(expr);
	if (!boost::starts_with(trimmedExpr, "return")) {
		trimmedExpr = "return(" + trimmedExpr + ");";
	}

	int retVals = luaEval(Arabica::DOM::Element<std::string>(), trimmedExpr);

	if (retVals == 1 && lua_isboolean(_luaState, -1)) {
		bool result = lua_toboolean(_luaState, -1);
		lua_pop(_luaState, 1);
		return result;
	}
	lua_pop(_luaState, retVals);
	return false;
}


std::string LuaDataModel::evalAsString(const std::string& expr) {
	std::string trimmedExpr = boost::trim_copy(expr);
	if (!boost::starts_with(trimmedExpr, "return")) {
		trimmedExpr = "return(" + trimmedExpr + ")";
	}

	int retVals = luaEval(Arabica::DOM::Element<std::string>(), trimmedExpr);

	if (retVals == 1 && lua_isstring(_luaState, -1)) {
		std::string result = lua_tostring(_luaState, -1);
		lua_pop(_luaState, 1);
		return result;
	}
	lua_pop(_luaState, retVals);
	return "";
}

std::string LuaDataModel::andExpressions(std::list<std::string> exprs) {
	std::stringstream exprSS;
	std::list<std::string>::const_iterator listIter;
	std::string andExpr;
	for (listIter = exprs.begin(); listIter != exprs.end(); listIter++) {
		exprSS << andExpr << *listIter;
		andExpr = " && ";
	}
	return exprSS.str();
}


}