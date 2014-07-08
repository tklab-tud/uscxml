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

LuaDataModel::LuaDataModel() {
	_luaState = NULL;
}

static int luaEventData(lua_State * l);
static int luaEventOrigin(lua_State * l);
static int luaEventOriginType(lua_State * l);
static int luaEventRaw(lua_State * l);
static int luaEventXML(lua_State * l);
static int luaEventName(lua_State * l);
static int luaEventContent(lua_State * l);
static int luaEventSendId(lua_State * l);
static int luaEventInvokeId(lua_State * l);
static int luaEventDestructor(lua_State * l);

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

	luabridge::getGlobalNamespace(dm->_luaState).beginClass<InterpreterImpl>("__interpreter").endClass();
	luabridge::getGlobalNamespace(dm->_luaState).addCFunction("In", luaInFunction);

	luabridge::setGlobal(dm->_luaState, dm->_interpreter, "__interpreter");

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

void LuaDataModel::setEvent(const Event& event) {
}

Data LuaDataModel::getStringAsData(const std::string& content) {
	Data data = Data::fromJSON(content);
	if (data.empty()) {
		data = Data(content, Data::VERBATIM);
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
	return 0;
}

void LuaDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
}

void LuaDataModel::eval(const Arabica::DOM::Element<std::string>& scriptElem,
                        const std::string& expr) {

}

bool LuaDataModel::isDeclared(const std::string& expr) {
	return true;
}

void LuaDataModel::assign(const Arabica::DOM::Element<std::string>& assignElem,
                          const Arabica::DOM::Node<std::string>& node,
                          const std::string& content) {

}

void LuaDataModel::assign(const std::string& location, const Data& data) {

}

void LuaDataModel::init(const Arabica::DOM::Element<std::string>& dataElem,
                        const Arabica::DOM::Node<std::string>& node,
                        const std::string& content) {

}

void LuaDataModel::init(const std::string& location, const Data& data) {

}

/**
 * The boolean expression language consists of the In predicate only. It has the
 * form 'In(id)', where id is the id of a state in the enclosing state machine.
 * The predicate must return 'true' if and only if that state is in the current
 * state configuration.
 */
bool LuaDataModel::evalAsBool(const Arabica::DOM::Node<std::string>& node, const std::string& expr) {
	// we need the result of the expression on the lua stack -> has to "return"!
	std::string trimmedExpr = boost::trim_copy(expr);
	if (!boost::starts_with(trimmedExpr, "return")) {
		trimmedExpr = "return(" + trimmedExpr + ")";
	}
	int error = luaL_loadstring(_luaState, trimmedExpr.c_str()) || lua_pcall(_luaState, 0, LUA_MULTRET, 0);
	if (error) {
		std::string errMsg = lua_tostring(_luaState, -1);
		lua_pop(_luaState, 1);  /* pop error message from the stack */
		ERROR_EXECUTION_THROW(errMsg);
	}
	int stackSize = lua_gettop(_luaState);
	if (stackSize != 1)
		return false;
	if (lua_isboolean(_luaState, -1))
		return lua_toboolean(_luaState, -1);
	return false;
}


std::string LuaDataModel::evalAsString(const std::string& expr) {
	return expr;
}

double LuaDataModel::evalAsNumber(const std::string& expr) {
	return 0;
}

}