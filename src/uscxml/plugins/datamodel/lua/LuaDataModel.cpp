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

#include "uscxml/Common.h"
#include "uscxml/util/URL.h"
#include "uscxml/util/String.h"

#include "LuaDataModel.h"

// disable forcing to bool performance warning
#pragma warning(push)
#pragma warning(disable : 4800)
#include "LuaBridge.h"
#pragma warning(pop)

#include "uscxml/messages/Event.h"
#include "uscxml/util/DOM.h"
#include "uscxml/interpreter/Logging.h"
#include <boost/algorithm/string.hpp>

//#include "LuaDOM.cpp.inc"

namespace uscxml {

//static int luaInspect(lua_State * l) {
//	return 0;
//}

bool _luaHasXMLParser = false;

static int luaEval(lua_State* luaState, const std::string& expr) {
	int preStack = lua_gettop(luaState);
	int error = luaL_loadstring(luaState, expr.c_str()) || lua_pcall(luaState, 0, LUA_MULTRET, 0);
	if (error) {
		std::string errMsg = lua_tostring(luaState, -1);
		lua_pop(luaState, 1);  /* pop error message from the stack */
		ERROR_EXECUTION_THROW(errMsg);
	}
	int postStack = lua_gettop(luaState);
	return postStack - preStack;
}

static Data getLuaAsData(lua_State* _luaState, const luabridge::LuaRef& lua) {
	Data data;
	if (lua.isFunction()) {
		// TODO: this might lead to a stack-overflow
		luabridge::LuaRef luaEvald = lua();
		return getLuaAsData(_luaState, luaEvald);
	} else if(lua.isLightUserdata() || lua.isUserdata()) {
		// not sure what to do
	} else if(lua.isThread()) {
		// not sure what to do
	} else if(lua.isNil()) {
		data.atom = "nil";
		data.type = Data::INTERPRETED;
	} else if(lua.isNumber()) {
		data.atom = toStr(lua.cast<double>());
		data.type = Data::INTERPRETED;
	} else if(lua.isString()) {
		data.atom = lua.cast<std::string>();
		data.type = Data::VERBATIM;
	} else if(lua.isTable()) {
		bool isArray = false;
		bool isMap = false;
		for (luabridge::Iterator iter (lua); !iter.isNil(); ++iter) {
			luabridge::LuaRef luaKey = iter.key();
			luabridge::LuaRef luaVal = *iter;
			if (luaKey.isString()) {
				assert(!isArray);
				isMap = true;
				// luaKey.tostring() is not working?! see issue84
				data.compound[luaKey.cast<std::string>()] = getLuaAsData(_luaState, luaVal);
			} else {
				assert(!isMap);
				isArray = true;
				data.array.push_back(getLuaAsData(_luaState, luaVal));
			}
		}
	}
	return data;
}

static luabridge::LuaRef getDataAsLua(lua_State* _luaState, const Data& data) {
	luabridge::LuaRef luaData (_luaState);

	if (data.node) {
		if (_luaHasXMLParser) {
			const luabridge::LuaRef& luaLom = luabridge::getGlobal(_luaState, "lxp.lom");
			const luabridge::LuaRef& luaLomParse = luaLom["parse"];
			assert(luaLomParse.isFunction());
			std::stringstream luaXMLSS;
			luaXMLSS << data.node;
			try {
				luaData = luaLomParse(luaXMLSS.str());
			} catch (luabridge::LuaException e) {
				ERROR_EXECUTION_THROW(e.what());
			}
			return luaData;
		}
	}
	if (data.compound.size() > 0) {
		luaData = luabridge::newTable(_luaState);
		std::map<std::string, Data>::const_iterator compoundIter = data.compound.begin();
		while(compoundIter != data.compound.end()) {
			luaData[compoundIter->first] = getDataAsLua(_luaState, compoundIter->second);
			compoundIter++;
		}
//		luaData["inspect"] = luaInspect;
		return luaData;
	}
	if (data.array.size() > 0) {
		luaData = luabridge::newTable(_luaState);
		std::list<Data>::const_iterator arrayIter = data.array.begin();
//		uint32_t index = 0;
		while(arrayIter != data.array.end()) {
//            luaData[index++] = getDataAsLua(_luaState, *arrayIter);
			luaData.append(getDataAsLua(_luaState, *arrayIter));
			arrayIter++;
		}
//		luaData["inspect"] = luaInspect;
		return luaData;
	}
	if (data.atom.size() > 0) {
		switch (data.type) {
		case Data::VERBATIM: {
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
				int retVals = luaEval(_luaState, "return(" + data.atom + ");");
				if (retVals == 1) {
					luaData = luabridge::LuaRef::fromStack(_luaState, -1);
				}
				lua_pop(_luaState, retVals);
			}
		}
		}
		return luaData;
	}
	// hopefully this is nil
	return luabridge::LuaRef(_luaState);
}

LuaDataModel::LuaDataModel() {
	_luaState = NULL;
}

int LuaDataModel::luaInFunction(lua_State * l) {
	luabridge::LuaRef ref = luabridge::getGlobal(l, "__datamodel");
	LuaDataModel* dm = ref.cast<LuaDataModel*>();

	int stackSize = lua_gettop(l);
	for (size_t i = 0; i < stackSize; i++) {
		if (!lua_isstring(l, -1 - i))
			continue;
		std::string stateName = lua_tostring(l, -1 - i);
		if (dm->_callbacks->isInState(stateName))
			continue;
		lua_pushboolean(l, 0);
		return 1;
	}
	lua_pushboolean(l, 1);
	return 1;
}

std::shared_ptr<DataModelImpl> LuaDataModel::create(DataModelCallbacks* callbacks) {
	std::shared_ptr<LuaDataModel> dm(new LuaDataModel());
	dm->_callbacks = callbacks;
	dm->_luaState = luaL_newstate();
	luaL_openlibs(dm->_luaState);

	try {
		const luabridge::LuaRef& requireFunc = luabridge::getGlobal(dm->_luaState, "require");
		const luabridge::LuaRef& resultLxp = requireFunc("lxp");
		const luabridge::LuaRef& resultLxpLOM = requireFunc("lxp.lom");

		// MSVC compiler bug with implicit cast operators, see comments in LuaRef class
		if ((bool)resultLxp && (bool)resultLxpLOM) {
			_luaHasXMLParser = true;
			luabridge::setGlobal(dm->_luaState, resultLxp, "lxp");
			luabridge::setGlobal(dm->_luaState, resultLxpLOM, "lxp.lom");
		}
	} catch (luabridge::LuaException e) {
		LOG(_callbacks->getLogger(), USCXML_INFO) << e.what();
	}

	luabridge::getGlobalNamespace(dm->_luaState).beginClass<LuaDataModel>("DataModel").endClass();
	luabridge::setGlobal(dm->_luaState, dm.get(), "__datamodel");

	luabridge::getGlobalNamespace(dm->_luaState).addCFunction("In", luaInFunction);

	luabridge::LuaRef ioProcTable = luabridge::newTable(dm->_luaState);
	std::map<std::string, IOProcessor> ioProcs = dm->_callbacks->getIOProcessors();
	std::map<std::string, IOProcessor>::const_iterator ioProcIter = ioProcs.begin();
	while(ioProcIter != ioProcs.end()) {
		Data ioProcData = ioProcIter->second.getDataModelVariables();
		ioProcTable[ioProcIter->first] = getDataAsLua(dm->_luaState, ioProcData);
		ioProcIter++;
	}
	luabridge::setGlobal(dm->_luaState, ioProcTable, "_ioprocessors");

	luabridge::LuaRef invTable = luabridge::newTable(dm->_luaState);
	std::map<std::string, Invoker> invokers = dm->_callbacks->getInvokers();
	std::map<std::string, Invoker>::const_iterator invIter = invokers.begin();
	while(invIter != invokers.end()) {
		Data invData = invIter->second.getDataModelVariables();
		invTable[invIter->first] = getDataAsLua(dm->_luaState, invData);
		invIter++;
	}
	luabridge::setGlobal(dm->_luaState, invTable, "_invokers");

	luabridge::setGlobal(dm->_luaState, dm->_callbacks->getName(), "_name");
	luabridge::setGlobal(dm->_luaState, dm->_callbacks->getSessionId(), "_sessionid");

	return dm;
}

LuaDataModel::~LuaDataModel() {
	if (_luaState != NULL)
		lua_close(_luaState);
}

void LuaDataModel::addExtension(DataModelExtension* ext) {
	ERROR_EXECUTION_THROW("Extensions unimplemented in lua datamodel");
}

void LuaDataModel::setEvent(const Event& event) {
	luabridge::LuaRef luaEvent(_luaState);
	luaEvent = luabridge::newTable(_luaState);

	luaEvent["name"] = event.name;
	if (event.raw.size() > 0)
		luaEvent["raw"] = event.raw;
	if (event.origin.size() > 0)
		luaEvent["origin"] = event.origin;
	if (event.origintype.size() > 0)
		luaEvent["origintype"] = event.origintype;
	if (event.invokeid.size() > 0)
		luaEvent["invokeid"] = event.invokeid;
	if (!event.hideSendId)
		luaEvent["sendid"] = event.sendid;
//	luaEvent["inspect"] = luaInspect;

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

	if (event.data.node) {
		if (_luaHasXMLParser) {
			const luabridge::LuaRef& luaLom = luabridge::getGlobal(_luaState, "lxp.lom");
			const luabridge::LuaRef& luaLomParse = luaLom["parse"];
			assert(luaLomParse.isFunction());
			std::stringstream luaXMLSS;
			luaXMLSS << event.data.node;
			try {
				luaEvent["data"] = luaLomParse(luaXMLSS.str());
			} catch (luabridge::LuaException e) {
				ERROR_EXECUTION_THROW(e.what());
			}
		} else {
			ERROR_EXECUTION_THROW("No DOM support in Lua datamodel");
		}
	} else {
		// _event.data is KVP
		Data d = event.data;

		if (!event.params.empty()) {
			Event::params_t::const_iterator paramIter = event.params.begin();
			while(paramIter != event.params.end()) {
				d.compound[paramIter->first] = paramIter->second;
				paramIter++;
			}
		}
		if (!event.namelist.empty()) {
			Event::namelist_t::const_iterator nameListIter = event.namelist.begin();
			while(nameListIter != event.namelist.end()) {
				d.compound[nameListIter->first] = nameListIter->second;
				nameListIter++;
			}
		}

		if (!d.empty()) {
			luabridge::LuaRef luaData = getDataAsLua(_luaState, d);
			assert(luaEvent.isTable());
			// assert(luaData.isTable()); // not necessarily test179
			luaEvent["data"] = luaData;
		}
	}

	luabridge::setGlobal(_luaState, luaEvent, "_event");
}

Data LuaDataModel::evalAsData(const std::string& content) {
	Data data;
	ErrorEvent originalError;

	std::string trimmedExpr = boost::trim_copy(content);

	try {
		int retVals = luaEval(_luaState, "return(" + trimmedExpr + ")");
		if (retVals == 1) {
			data = getLuaAsData(_luaState, luabridge::LuaRef::fromStack(_luaState, -1));
		}
		lua_pop(_luaState, retVals);
		return data;
	} catch (ErrorEvent e) {
		originalError = e;
	}

	int retVals = 0;
	try {
		// evaluate again without the return()
		retVals = luaEval(_luaState, trimmedExpr);
	} catch (ErrorEvent e) {
		throw originalError; // we will assume syntax error and throw
	}

	if (retVals == 0)
		throw originalError; // we will assume syntax error and throw


	try {
		if (retVals == 1) {
			data = getLuaAsData(_luaState, luabridge::LuaRef::fromStack(_luaState, -1));
		}
		lua_pop(_luaState, retVals);
		return data;

	} catch (ErrorEvent e) {
		throw e; // we will assume syntax error and throw
	}


	return data;
}

bool LuaDataModel::isValidSyntax(const std::string& expr) {
	int preStack = lua_gettop(_luaState);
	int err = luaL_loadstring (_luaState, expr.c_str());

	// clean stack again
	lua_pop(_luaState, lua_gettop(_luaState) - preStack);


	if (err == LUA_ERRSYNTAX)
		return false;

	return true;
}

uint32_t LuaDataModel::getLength(const std::string& expr) {
	// we need the result of the expression on the lua stack -> has to "return"!
	std::string trimmedExpr = boost::trim_copy(expr);

	if (!boost::starts_with(trimmedExpr, "return")) {
		trimmedExpr = "return(#" + trimmedExpr + ")";
	}

	int retVals = luaEval(_luaState, trimmedExpr);

#if 1

	if (retVals == 1 && lua_isnumber(_luaState, -1)) {
		int result = lua_tointeger(_luaState, -1);
		lua_pop(_luaState, 1);
		return result;
	}

	lua_pop(_luaState, retVals);
	ERROR_EXECUTION_THROW("'" + expr + "' does not evaluate to an array.");
	return 0;
#else

	if (retVals == 1) {
		luabridge::LuaRef luaData = luabridge::LuaRef::fromStack(_luaState, -1);
		if (luaData.isNumber()) {
			lua_pop(_luaState, retVals);
			return luaData.cast<int>();
		}
	}
	lua_pop(_luaState, retVals);

	ERROR_EXECUTION_THROW("'" + expr + "' does not evaluate to an array.");
	return 0;

#endif
}

void LuaDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
	iteration++; // test153: arrays start at 1

	const luabridge::LuaRef& arrRef = luabridge::getGlobal(_luaState, array.c_str());
	if (arrRef.isTable()) {

		// triggers syntax error for invalid items, test 152
		int retVals = luaEval(_luaState, item + " = " + array + "[" + toStr(iteration) + "]");
		lua_pop(_luaState, retVals);

		if (index.length() > 0) {
			int retVals = luaEval(_luaState, index + " = " + toStr(iteration));
			lua_pop(_luaState, retVals);
		}
	}
}

bool LuaDataModel::isDeclared(const std::string& expr) {
	// see: http://lua-users.org/wiki/DetectingUndefinedVariables
	return true;
}


void LuaDataModel::assign(const std::string& location, const Data& data) {
	if (location.length() == 0) {
		ERROR_EXECUTION_THROW("Assign element has neither id nor location");
	}

	// flags on attribute are ignored?
	if (location.compare("_sessionid") == 0) // test 322
		ERROR_EXECUTION_THROW("Cannot assign to _sessionId");
	if (location.compare("_name") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _name");
	if (location.compare("_ioprocessors") == 0)  // test 326
		ERROR_EXECUTION_THROW("Cannot assign to _ioprocessors");
	if (location.compare("_invokers") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _invokers");
	if (location.compare("_event") == 0)
		ERROR_EXECUTION_THROW("Cannot assign to _event");

	if (data.node) {
		ERROR_EXECUTION_THROW("Cannot assign xml nodes in lua datamodel");

		// TODO: DOM is prepared by swig

//        return SWIG_JSC_NewPointerObj(_ctx,
//                                      (void*)node,
//                                      SWIG_TypeDynamicCast(SWIGTYPE_p_XERCES_CPP_NAMESPACE__DOMNode,
//                                                           SWIG_as_voidptrptr(&node)),
//                                      0);


//        JSObjectSetProperty(_ctx, JSContextGetGlobalObject(_ctx), JSStringCreateWithUTF8CString(location.c_str()), getNodeAsValue(data.node), 0, &exception);
	} else {

		// trigger error.execution for undefined locations, test286 test311
		int retVals = luaEval(_luaState, location + " = " + location);
		lua_pop(_luaState, retVals);

		std::list<std::pair<std::string, bool> > idPath;
		size_t start = 0;
		for (size_t i = 0; i < location.size(); i++) {
			if (location[i] == '.' || location[i] == '[') {
				idPath.push_back(std::make_pair(location.substr(start, i - start), false));
				start = i + 1;
			} else if (location[i] == ']') {
				idPath.push_back(std::make_pair(location.substr(start, i - start), true));
				start = i + 1;
			}
		}
		if (start < location.size())
			idPath.push_back(std::make_pair(location.substr(start, location.size() - start), false));

		if (idPath.size() == 0)
			return;

		luabridge::LuaRef lua = getDataAsLua(_luaState, data);

		if (idPath.size() == 1) {
			// trivial case where we reference a simple toplevel identifier
			luabridge::setGlobal(_luaState, lua, location.c_str());

		} else {
			auto globalId = idPath.front();
			idPath.pop_front();

			auto field = idPath.back();
			idPath.pop_back();

			luabridge::LuaRef topValue = luabridge::getGlobal(_luaState, globalId.first.c_str());
			luabridge::LuaRef value = topValue;

			for (auto ident : idPath) {
				if (!value.isTable())
					value = luabridge::newTable(_luaState);

				if (ident.second) {
					luabridge::LuaRef tmp = value[strTo<long>(ident.first)];
				} else {
					luabridge::LuaRef tmp = value[ident];
					value = tmp;
				}
			}
			if (field.second) {
				value[strTo<long>(field.first)] = lua;
			} else {
				value[field.first] = lua;
			}

		}


//        std::cout << Data::toJSON(evalAsData(location)) << std::endl;
	}
}

void LuaDataModel::init(const std::string& location, const Data& data) {
	luabridge::setGlobal(_luaState, luabridge::Nil(), location.c_str());
	assign(location, data);
}

bool LuaDataModel::evalAsBool(const std::string& expr) {
	// we need the result of the expression on the lua stack -> has to "return"!
	std::string trimmedExpr = boost::trim_copy(expr);

	int retVals = luaEval(_luaState, "return(" + trimmedExpr + ")");

	if (retVals == 1) {
		bool result = lua_toboolean(_luaState, -1);
		lua_pop(_luaState, 1);
		return result;
	}
	lua_pop(_luaState, retVals);

	return false;
}

Data LuaDataModel::getAsData(const std::string& content) {
	Data data;
	std::string trimmedExpr = boost::trim_copy(content);

	int retVals = luaEval(_luaState, "__tmp = " + content + "; return __tmp");
	if (retVals == 1) {
		data = getLuaAsData(_luaState, luabridge::LuaRef::fromStack(_luaState, -1));
	}
	lua_pop(_luaState, retVals);

	// escape as a string, this is sometimes the case with <content>
	if (data.atom == "nil" && data.type == Data::INTERPRETED) {
		int retVals = luaEval(_luaState, "__tmp = '" + content + "'; return __tmp");
		if (retVals == 1) {
			data = getLuaAsData(_luaState, luabridge::LuaRef::fromStack(_luaState, -1));
		}
		lua_pop(_luaState, retVals);
	}

	return data;
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
