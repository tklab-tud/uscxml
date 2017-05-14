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
#include "uscxml/util/String.h"
#include "PromelaDataModel.h"
#ifndef NO_XERCESC
#include "uscxml/util/DOM.h"
#endif
#include <cctype>
#include <boost/algorithm/string.hpp>

#include "PromelaParser.h"
#include "parser/promela.tab.hpp"
#include "uscxml/interpreter/Logging.h"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

#define INVALID_ASSIGNMENT(name) \
name.compare("_sessionid") == 0 || \
name.compare("_name") == 0 || \
name.compare("_ioprocessors") == 0 || \
name.compare("_event") == 0

namespace uscxml {

#ifdef BUILD_AS_PLUGINS
PLUMA_CONNECTOR
bool pluginConnect(pluma::Host& host) {
	host.add( new PromelaDataModelProvider() );
	return true;
}
#endif

PromelaDataModel::PromelaDataModel() {
}

PromelaDataModel::~PromelaDataModel() {
}

std::shared_ptr<DataModelImpl> PromelaDataModel::create(DataModelCallbacks* callbacks) {
	std::shared_ptr<PromelaDataModel> dm(new PromelaDataModel());

	dm->_callbacks = callbacks;
	dm->setup();
	return dm;
}

void PromelaDataModel::setup() {
	// session id
	Data sessionId;
	sessionId.compound["type"] = Data("string", Data::VERBATIM);
	sessionId.compound["value"] = Data(_callbacks->getSessionId(), Data::VERBATIM);
	_variables["_sessionid"] = sessionId;

	// name
	Data name;
	name.compound["type"] = Data("string", Data::VERBATIM);
	name.compound["value"] = Data(_callbacks->getName(), Data::VERBATIM);
	_variables["_name"] = name;

	// ioprocessors
	Data ioProcs;
	ioProcs.compound["type"] = Data("compound", Data::VERBATIM);

	std::map<std::string, IOProcessor> ioProcessors = _callbacks->getIOProcessors();
	for (std::map<std::string, IOProcessor>::iterator iter = ioProcessors.begin(); iter != ioProcessors.end(); iter++) {
		ioProcs.compound["value"].compound[iter->first] = iter->second.getDataModelVariables();
	}
	_variables["_ioprocessors"] = ioProcs;

	_lastMType = 0;

}

void PromelaDataModel::setEvent(const Event& event) {
	Data variable;
	variable.compound["type"] = Data("compound", Data::VERBATIM);
	variable.compound["value"].compound["name"] = Data(event.name, Data::VERBATIM);
	variable.compound["value"].compound["origin"] = Data(event.origin, Data::VERBATIM);
	variable.compound["value"].compound["origintype"] = Data(event.origintype, Data::VERBATIM);
	variable.compound["value"].compound["invokeid"] = Data(event.invokeid, Data::VERBATIM);
	if (event.hideSendId) {
		variable.compound["value"].compound["sendid"] = Data("", Data::VERBATIM);
	} else {
		variable.compound["value"].compound["sendid"] = Data(event.sendid, Data::VERBATIM);
	}
	switch (event.eventType) {
	case Event::PLATFORM:
		variable.compound["value"].compound["type"] = Data("platform", Data::VERBATIM);
		break;
	case Event::INTERNAL:
		variable.compound["value"].compound["type"] = Data("internal", Data::VERBATIM);
		break;
	case Event::EXTERNAL:
		variable.compound["value"].compound["type"] = Data("external", Data::VERBATIM);
		break;
	default:
		variable.compound["value"].compound["type"] = Data("invalid", Data::VERBATIM);
		break;
	}

	if (false) {
#if 0
		else if (event.dom) {
			// no support
		} else if (event.content.length() > 0) {
			// _event.data is a string or JSON
			Data json = Data::fromJSON(event.content);
			if (!json.empty()) {
				variable.compound["value"].compound["data"] = json;
			} else {
				if (isNumeric(event.content.c_str(), 10)) {
					variable.compound["value"].compound["data"] = Data(event.content, Data::INTERPRETED);
				} else {
					variable.compound["value"].compound["data"] = Data(spaceNormalize(event.content), Data::VERBATIM);
				}
			}
#endif
		} else {
			// _event.data is KVP
			if (!event.data.empty()) {
				variable.compound["value"].compound["data"] = event.data;
			} else {
				// test 343 / test 488
				variable.compound["value"].compound["data"];
			}

			for (Event::params_t::const_iterator start = event.params.begin(), end = event.params.end();
			        start != end; start = event.params.upper_bound(start->first)) {
				// only set first param key
				if (isNumeric(start->second.atom.c_str(), 10)) {
					variable.compound["value"].compound["data"].compound[start->first] = Data(strTo<int>(start->second.atom));
				} else {
					variable.compound["value"].compound["data"].compound[start->first] = start->second;
				}
			}

			for (Event::namelist_t::const_iterator iter = event.namelist.begin(); iter != event.namelist.end(); iter++) {
				if (isNumeric(iter->second.atom.c_str(), 10)) {
					variable.compound["value"].compound["data"].compound[iter->first] = Data(strTo<int>(iter->second.atom));
				} else {
					variable.compound["value"].compound["data"].compound[iter->first] = iter->second;
				}
			}
		}

		// iterate all data elements and adapt type for int if atom is integer
		adaptType(variable.compound["value"].compound["data"]);

		_variables["_event"] = variable;
	}

	void PromelaDataModel::adaptType(Data& data) {
		if (data.atom.length() > 0 && isInteger(data.atom.c_str(), 10)) {
			data.type = Data::INTERPRETED;
			return;
		}

		if (data.array.size() > 0) {
			for (std::list<Data>::iterator iter = data.array.begin(); iter != data.array.end(); iter++) {
				adaptType(*iter);
			}
			return;
		}

		if (data.compound.size() > 0) {
			for (std::map<std::string, Data>::iterator iter = data.compound.begin(); iter != data.compound.end(); iter++) {
				adaptType(iter->second);
			}
			return;
		}

	}

	bool PromelaDataModel::isValidSyntax(const std::string& expr) {
		try {
			PromelaParser parser(expr);
		} catch (Event e) {
			LOG(_callbacks->getLogger(), USCXML_ERROR) << e << std::endl;
			return false;
		}
		return true;
	}

	uint32_t PromelaDataModel::getLength(const std::string& expr) {
		if (!isDeclared(expr)) {
			ERROR_EXECUTION_THROW("Variable '" + expr + "' was not declared");
		}

		if (!_variables[expr].hasKey("size")) {
			ERROR_EXECUTION_THROW("Variable '" + expr + "' is no array");
		}

		return strTo<int>(_variables[expr]["size"].atom);
	}

	void PromelaDataModel::setForeach(const std::string& item,
	                                  const std::string& array,
	                                  const std::string& index,
	                                  uint32_t iteration) {
		// assign array element to item
		std::stringstream ss;
		ss << array << "[" << iteration << "]";

		PromelaParser itemParser(item, 1, PromelaParser::PROMELA_EXPR);
		if (itemParser.ast->type != PML_NAME)
			ERROR_EXECUTION_THROW("Expression '" + item + "' is no valid item");

		PromelaParser arrayParser(ss.str(), 1, PromelaParser::PROMELA_EXPR);

		try {
			setVariable(itemParser.ast, getVariable(arrayParser.ast));
		} catch (ErrorEvent e) {
			// test150
			PromelaParser itemDeclParser("int " + item); // this is likely the wrong type
			evaluateDecl(itemDeclParser.ast);
			setVariable(itemParser.ast, getVariable(arrayParser.ast));
		}

		if (index.length() > 0) {
			PromelaParser indexParser(index, 1, PromelaParser::PROMELA_EXPR);
			try {
				setVariable(indexParser.ast, Data(iteration));
			} catch (ErrorEvent e) {
				// test150
				PromelaParser indexDeclParser("int " + index);
				evaluateDecl(indexDeclParser.ast);
				setVariable(indexParser.ast, Data(iteration));
			}
		}

	}

	bool PromelaDataModel::evalAsBool(const std::string& expr) {
		PromelaParser parser(expr, 1, PromelaParser::PROMELA_EXPR);
//	parser.dump();
		Data tmp = evaluateExpr(parser.ast);

		if (tmp.atom.compare("false") == 0)
			return false;
		if (tmp.atom.compare("0") == 0)
			return false;
		return true;
	}

	Data PromelaDataModel::evalAsData(const std::string& expr) {
		PromelaParser parser(expr);
		return evaluateExpr(parser.ast);
	}

	Data PromelaDataModel::getAsData(const std::string& content) {
		try {
			return evalAsData(content);
		} catch (ErrorEvent e) {
			return Data::fromJSON(content);
		}
	}

	void PromelaDataModel::evaluateDecl(const std::string& expr) {
		PromelaParser parser(expr, 1, PromelaParser::PROMELA_DECL);
		evaluateDecl(parser.ast);
	}

	Data PromelaDataModel::evaluateExpr(const std::string& expr) {
		PromelaParser parser(expr, 1, PromelaParser::PROMELA_EXPR);
		return evaluateExpr(parser.ast);
	}

	void PromelaDataModel::evaluateStmnt(const std::string& expr) {
		PromelaParser parser(expr, 1, PromelaParser::PROMELA_STMNT);
		evaluateStmnt(parser.ast);
	}

	void PromelaDataModel::evaluateDecl(void* ast) {
		PromelaParserNode* node = (PromelaParserNode*)ast;
//	node->dump();
		if (false) {
		} else if (node->type == PML_DECL) {
			std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
			PromelaParserNode* vis = *opIter++;
			PromelaParserNode* type = *opIter++;
			PromelaParserNode* varlist = *opIter++;

			for (std::list<PromelaParserNode*>::iterator nameIter = varlist->operands.begin();
			        nameIter != varlist->operands.end();
			        nameIter++) {
				Data variable;
				variable.compound["vis"] = Data(vis->value, Data::VERBATIM);
				variable.compound["type"] = Data(type->value, Data::VERBATIM);

				if (false) {
				} else if ((*nameIter)->type == PML_NAME) {
					// plain variables without initial assignment

					if (type->value == "mtype") {
						variable.compound["value"] = Data(_lastMType++, Data::INTERPRETED);
					} else {
						variable.compound["value"] = Data(0, Data::INTERPRETED);
					}
					_variables.compound[(*nameIter)->value] = variable;

				} else if ((*nameIter)->type == PML_ASGN) {
					// initially assigned variables

					std::list<PromelaParserNode*>::iterator opIterAsgn = (*nameIter)->operands.begin();
					PromelaParserNode* name = *opIterAsgn++;
					PromelaParserNode* expr = *opIterAsgn++;

					try {
						variable.compound["value"] = evaluateExpr(expr);
					} catch(uscxml::Event e) {
						// test277, declare and throw
						_variables.compound[name->value] = variable;
						throw e;
					}

					assert(opIterAsgn == (*nameIter)->operands.end());
					_variables.compound[name->value] = variable;
				} else if ((*nameIter)->type == PML_VAR_ARRAY) {
					// variable arrays

					std::list<PromelaParserNode*>::iterator opIterAsgn = (*nameIter)->operands.begin();
					PromelaParserNode* name = *opIterAsgn++;
					int size = dataToInt(evaluateExpr(*opIterAsgn++));

					variable.compound["size"] = Data(size);
					for (int i = 0; i < size; i++) {
						variable.compound["value"].array.push_back(Data(0, Data::INTERPRETED));
					}

					assert(opIterAsgn == (*nameIter)->operands.end());
					_variables.compound[name->value] = variable;

				} else {
					ERROR_EXECUTION_THROW("Declaring variables via " + PromelaParserNode::typeToDesc((*nameIter)->type) + " not implemented");
				}
			}
			assert(opIter == node->operands.end());
		} else if (node->type == PML_DECLLIST) {
			for (std::list<PromelaParserNode*>::iterator declIter = node->operands.begin();
			        declIter != node->operands.end();
			        declIter++) {
				evaluateDecl(*declIter);
			}
		} else {
			node->dump();
			ERROR_EXECUTION_THROW("Declaring variables via " + PromelaParserNode::typeToDesc(node->type) + " not implemented");
		}
	}

	int PromelaDataModel::dataToInt(const Data& data) {
//		if (data.type != Data::INTERPRETED)
//			ERROR_EXECUTION_THROW("Operand is not integer");
		int value = strTo<int>(data.atom);
		if (data.atom.compare(toStr(value)) != 0)
			ERROR_EXECUTION_THROW("Operand is not integer");
		return value;
	}

	bool PromelaDataModel::dataToBool(const Data& data) {
		if (data.atom.size() == 0) // empty string or undefined
			return false;

		if (data.type == Data::VERBATIM) {
			// non-empty string is true
			return true;
		} else {
			if (data.atom.compare("true") == 0) {
				// boolean true is true
				return true;
			} else if (data.atom.compare("false") == 0) {
				return false;
			} else if (dataToInt(data) != 0) {
				return true; // non zero values are true
			}
		}
		return false;
	}

	Data PromelaDataModel::evaluateExpr(void* ast) {
		PromelaParserNode* node = (PromelaParserNode*)ast;
		std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
		switch (node->type) {
		case PML_CONST:
			if (iequals(node->value, "false"))
				return Data(false);
			if (iequals(node->value, "true"))
				return Data(true);
			return Data(strTo<int>(node->value));
		case PML_NAME: {
			Data d = getVariable(node);
			if (d.atom.size() != 0)
				// fixes issue 127
				if (isNumeric(d.atom.c_str(), 10)) {
					return Data(d.atom, Data::VERBATIM);
				}
			return Data(d.asJSON(), Data::VERBATIM);
			if (d.type == Data::INTERPRETED && d.atom[0] == '\'' && d.atom[d.atom.size() - 1] == '\'')
				return Data(d.atom.substr(1, d.atom.size() - 2), Data::VERBATIM);
			return d;
		}
		case PML_VAR_ARRAY:
		case PML_CMPND:
			return getVariable(node);
		case PML_STRING: {
			std::string stripped = node->value.substr(1, node->value.size() - 2);
			return Data(stripped, Data::VERBATIM);
//		return Data(node->value, Data::INTERPRETED);
		}
		case PML_PLUS:
			return Data(dataToInt(evaluateExpr(*opIter++)) + dataToInt(evaluateExpr(*opIter++)));
		case PML_MINUS:
			return Data(dataToInt(evaluateExpr(*opIter++)) - dataToInt(evaluateExpr(*opIter++)));
		case PML_DIVIDE:
			return Data(dataToInt(evaluateExpr(*opIter++)) / dataToInt(evaluateExpr(*opIter++)));
		case PML_MODULO:
			return Data(dataToInt(evaluateExpr(*opIter++)) % dataToInt(evaluateExpr(*opIter++)));
		case PML_EQ: {
			PromelaParserNode* lhs = *opIter++;
			PromelaParserNode* rhs = *opIter++;

			Data left = evaluateExpr(lhs);
			Data right = evaluateExpr(rhs);

			if (left == right) // overloaded operator==
				return Data(true);

			// literal strings or strings in variables
			if ((lhs->type == PML_STRING || rhs->type == PML_STRING)
			        || (left.type == Data::VERBATIM && right.type == Data::VERBATIM)) {
				return (left.atom.compare(right.atom) == 0 ? Data(true) : Data(false));
			}
			return Data(dataToInt(left) == dataToInt(right));
		}
		case PML_NEG:
			return Data(!dataToBool(evaluateExpr(*opIter++)));
		case PML_LT:
			return Data(dataToInt(evaluateExpr(*opIter++)) < dataToInt(evaluateExpr(*opIter++)));
		case PML_LE:
			return Data(dataToInt(evaluateExpr(*opIter++)) <= dataToInt(evaluateExpr(*opIter++)));
		case PML_GT:
			return Data(dataToInt(evaluateExpr(*opIter++)) > dataToInt(evaluateExpr(*opIter++)));
		case PML_GE:
			return Data(dataToInt(evaluateExpr(*opIter++)) >= dataToInt(evaluateExpr(*opIter++)));
		case PML_TIMES:
			return Data(dataToInt(evaluateExpr(*opIter++)) * dataToInt(evaluateExpr(*opIter++)));
		case PML_LSHIFT:
			return Data(dataToInt(evaluateExpr(*opIter++)) << dataToInt(evaluateExpr(*opIter++)));
		case PML_RSHIFT:
			return Data(dataToInt(evaluateExpr(*opIter++)) >> dataToInt(evaluateExpr(*opIter++)));
		case PML_ASGN: {
			PromelaParserNode* lhs = *opIter++;
			PromelaParserNode* rhs = *opIter++;
			setVariable(lhs, evaluateExpr(rhs));
			break;
		}
		case PML_AND:
		case PML_OR: {
			PromelaParserNode* lhs = *opIter++;
			PromelaParserNode* rhs = *opIter++;

//		std::cout << "-----" << std::endl;
//		lhs->dump();
//		rhs->dump();

			Data left = evaluateExpr(lhs);
			Data right = evaluateExpr(rhs);

			bool truthLeft = dataToBool(left);
			bool truthRight = dataToBool(right);

			if (node->type == PML_AND) {
				return Data(truthLeft && truthRight);
			} else {
				return Data(truthLeft || truthRight);
			}
		}
		default:
			ERROR_EXECUTION_THROW("Support for " + PromelaParserNode::typeToDesc(node->type) + " expressions not implemented");
		}
		return Data(0, Data::INTERPRETED);
	}

	void PromelaDataModel::evaluateStmnt(void* ast) {
		PromelaParserNode* node = (PromelaParserNode*)ast;
		std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
		switch (node->type) {
		case PML_ASGN: {
			PromelaParserNode* name = *opIter++;
			PromelaParserNode* expr = *opIter++;
			setVariable(name, evaluateExpr(expr));
			break;
		}
		case PML_STMNT: {
			while(opIter != node->operands.end()) {
				evaluateStmnt(*opIter++);
			}
			break;
		}
		case PML_INCR: {
			PromelaParserNode* name = *opIter++;
			setVariable(name, Data(strTo<long>(getVariable(name)) + 1));
			break;
		}
		case PML_DECR: {
			PromelaParserNode* name = *opIter++;
			setVariable(name, Data(strTo<long>(getVariable(name)) - 1));
			break;
		}
		default:
			node->dump();
			ERROR_EXECUTION_THROW("No support for " + PromelaParserNode::typeToDesc(node->type) + " statement implemented");
		}
	}


	void PromelaDataModel::setVariable(void* ast, const Data& value) {
		PromelaParserNode* node = (PromelaParserNode*)ast;

		if (INVALID_ASSIGNMENT(node->value)) {
			ERROR_EXECUTION_THROW("Cannot assign to " + node->value);
		}

		switch (node->type) {
		case PML_VAR_ARRAY: {
			std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();

			PromelaParserNode* name = *opIter++;
			PromelaParserNode* expr = *opIter++;

			if (!_variables.hasKey(name->value)) {
				ERROR_EXECUTION_THROW("Variable " + name->value + " is undeclared");
			}

			// is the location an array?
			if (!_variables[name->value].hasKey("size")) {
				ERROR_EXECUTION_THROW("Variable " + name->value + " is no array");
			}

			// is the array large enough?
			int index = dataToInt(evaluateExpr(expr));
			if (strTo<int>(_variables[name->value]["size"].atom) <= index) {
				ERROR_EXECUTION_THROW("Index " + toStr(index) + " in array " + name->value + "[" + _variables[name->value]["size"].atom + "] is out of bounds");
			}

			_variables.compound[name->value].compound["value"][index] = value;

			break;
		}
		case PML_NAME: {
			// location is an array, but no array was passed
			if (!_variables.hasKey(node->value)) {
				ERROR_EXECUTION_THROW("Variable " + node->value + " is undeclared");
			}

			if (_variables[node->value].hasKey("size")) {
				if (value.compound.size() > 0 || value.atom.size() > 0)
					ERROR_EXECUTION_THROW("Variable " + node->value + " is an array");

				if (strTo<size_t>(_variables[node->value].compound["size"].atom) < value.array.size())
					ERROR_EXECUTION_THROW("Array assigned to " + node->value + " is too large");
			}

			_variables.compound[node->value].compound["value"] = value;
			break;
		}
		case PML_CMPND: {
			std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
			PromelaParserNode* name = *opIter++;

			if (!_variables.hasKey(name->value)) {
				ERROR_EXECUTION_THROW("Variable " + name->value + " is undeclared");
			}

			// location is no array
			if (_variables[name->value].hasKey("size")) {
				ERROR_EXECUTION_THROW("Variable " + name->value + " is an array");
			}

//		std::cout << Data::toJSON(_variables) << std::endl;;

			Data* var = &_variables[name->value].compound["value"];
			var->compound["type"] = Data("compound", Data::VERBATIM);
			var->compound["vis"] = Data("", Data::VERBATIM);

			while(opIter != node->operands.end()) {
				name = *opIter;
				opIter++;
				var = &(var->compound[name->value]);
			}
			*var = value;

			break;
		}
		default:
			node->dump();
			ERROR_EXECUTION_THROW("No support for " + PromelaParserNode::typeToDesc(node->type) + " variables implemented");
			break;
		}

//	std::cout << Data::toJSON(_variables) << std::endl;
	}

	Data PromelaDataModel::getVariable(void* ast) {
		PromelaParserNode* node = (PromelaParserNode*)ast;
//	node->dump();

		std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
		switch(node->type) {
		case PML_NAME:
			if (_variables.compound.find(node->value) == _variables.compound.end()) {
				ERROR_EXECUTION_THROW("No variable " + node->value + " was declared");
			}
//		if (_variables[node->value].compound.find("size") != _variables[node->value].compound.end()) {
//			ERROR_EXECUTION_THROW("Type error: Variable " + node->value + " is an array");
//		}
			return _variables[node->value]["value"];
		case PML_VAR_ARRAY: {
			PromelaParserNode* name = *opIter++;
			PromelaParserNode* expr = *opIter++;
			int index = dataToInt(evaluateExpr(expr));

			if (_variables.compound.find(name->value) == _variables.compound.end()) {
				ERROR_EXECUTION_THROW("No variable " + name->value + " was declared");
			}

			if (!_variables[name->value].hasKey("size")) {
				ERROR_EXECUTION_THROW("Variable " + name->value + " is no array");
			}

			if (strTo<int>(_variables[name->value]["size"].atom) <= index) {
				ERROR_EXECUTION_THROW("Index " + toStr(index) + " in array " + name->value + "[" + _variables[name->value]["size"].atom + "] is out of bounds");
			}
			return _variables.compound[name->value].compound["value"][index];
		}
		case PML_CMPND: {
//		node->dump();
//		std::cout << Data::toJSON(_variables["_event"]);
			std::stringstream idPath;
			PromelaParserNode* name = *opIter++;

			// special case for _x variables
			if (name->value.compare("_x") == 0) {
				PromelaParserNode* what = *opIter++;

				if (what->type == PML_VAR_ARRAY) {
					if (what->operands.size() == 2) {
						std::string arrName = what->operands.front()->value;
						std::string index = what->operands.back()->value;

						if (what->operands.back()->type == PML_STRING) {
							index = index.substr(1, index.size() - 2); // remove quotes
						}

						if (arrName.compare("states") == 0) {
							return Data(_callbacks->isInState(index));
						}
					}
				}
				ERROR_EXECUTION_THROW("No variable " + name->value + " was declared");
			}

			if (_variables.compound.find(name->value) == _variables.compound.end()) {
				ERROR_EXECUTION_THROW("No variable " + name->value + " was declared");
			}

			Data currData = _variables.compound[name->value]["value"];
			idPath << name->value;
			while(opIter != node->operands.end()) {
				std::string key = (*opIter)->value;
				idPath << "." << key;
				if (currData.compound.find(key) == currData.compound.end()) {
					ERROR_EXECUTION_THROW("No variable " + idPath.str() + " was declared");
				}
				Data tmp = currData.compound[key];
				currData = tmp;

				opIter++;
			}
			return currData;
		}
		default:
			ERROR_EXECUTION_THROW("Retrieving value of " + PromelaParserNode::typeToDesc(node->type) + " variable not implemented");
		}
		return Data(0, Data::INTERPRETED);
	}

	void PromelaDataModel::assign(const std::string& location, const Data& data, const std::map<std::string, std::string>& attr) {
		PromelaParser parser(location);
		if (data.atom.size() > 0 && data.type == Data::INTERPRETED) {
			setVariable(parser.ast, evalAsData(data.atom));
		} else {
			setVariable(parser.ast, data);
		}
	}

	void PromelaDataModel::init(const std::string& location, const Data& data, const std::map<std::string, std::string>& attr) {
		{
			std::string type = (attr.find("type") != attr.end() ? attr.at("type") : "auto");
			std::string arrSize;

			size_t bracketPos = type.find("[");
			if (bracketPos != std::string::npos) {
				arrSize = type.substr(bracketPos, type.length() - bracketPos);
				type = type.substr(0, bracketPos);
			}

			std::string expr = type + " " + location + arrSize;
			PromelaParser parser(expr, 1, PromelaParser::PROMELA_DECL);
			evaluateDecl(parser.ast);
		}

		PromelaParser parser(location);
		if (data.atom.size() > 0 && data.type == Data::INTERPRETED) {
			Data d = Data::fromJSON(data);
			if (!d.empty())
				setVariable(parser.ast, Data::fromJSON(data));
			setVariable(parser.ast, data);
		} else {
			setVariable(parser.ast, data);
		}
	}

	bool PromelaDataModel::isDeclared(const std::string& expr) {
		PromelaParser parser(expr);
//	parser.dump();
		if (parser.ast->type == PML_VAR_ARRAY)
			return _variables.compound.find(parser.ast->operands.front()->value) != _variables.compound.end();

		if (parser.ast->type == PML_CMPND) {
			// JSON declaration
			std::list<PromelaParserNode*>::iterator opIter = parser.ast->operands.begin();
			Data* var = &_variables;

			while(opIter != parser.ast->operands.end()) {
				std::string name = (*opIter)->value;
				opIter++;
				if (var->compound.find(name) != var->compound.end()) {
					var = &(var->compound.at(name));
				} else if (var->compound.find("value") != var->compound.end() && var->compound.at("value").compound.find(name) != var->compound.at("value").compound.end()) {
					var = &(var->compound.at("value").compound.at(name));
				} else {
					return false;
				}
			}
			return true;

		}

		return _variables.compound.find(expr) != _variables.compound.end();
	}

	void PromelaDataModel::addExtension(DataModelExtension* ext) {
		ERROR_EXECUTION_THROW("Extensions unimplemented in promela datamodel");
	}


}
