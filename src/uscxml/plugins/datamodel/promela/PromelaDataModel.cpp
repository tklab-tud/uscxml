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
#include "uscxml/config.h"
#include "PromelaDataModel.h"
#include "uscxml/DOMUtils.h"
#include "uscxml/Message.h"
#include <glog/logging.h>
#include <cctype>

#include "PromelaParser.h"
#include "parser/promela.tab.hpp"

#ifdef BUILD_AS_PLUGINS
#include <Pluma/Connector.hpp>
#endif

namespace uscxml {

using namespace Arabica::XPath;
using namespace Arabica::DOM;

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

boost::shared_ptr<DataModelImpl> PromelaDataModel::create(InterpreterImpl* interpreter) {
	boost::shared_ptr<PromelaDataModel> dm = boost::shared_ptr<PromelaDataModel>(new PromelaDataModel());
	dm->_interpreter = interpreter;
	dm->_lastMType = 0;
	return dm;
}

void PromelaDataModel::registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor) {
}

void PromelaDataModel::setSessionId(const std::string& sessionId) {
	_sessionId = sessionId;
}

void PromelaDataModel::setName(const std::string& name) {
	_name = name;
}

void PromelaDataModel::pushContext() {
//	std::cout << "PromelaDataModel::pushContext" << std::endl;
}

void PromelaDataModel::popContext() {
//	std::cout << "PromelaDataModel::popContext" << std::endl;
}

void PromelaDataModel::initialize() {
//	std::cout << "PromelaDataModel::initialize" << std::endl;
}

void PromelaDataModel::setEvent(const Event& event) {
	_event = event;
}

Data PromelaDataModel::getStringAsData(const std::string& content) {
	Data data(content, Data::VERBATIM);
	return data;
}


bool PromelaDataModel::validate(const std::string& location, const std::string& schema) {
//	std::cout << "PromelaDataModel::validate" << std::endl;
	return true;
}

uint32_t PromelaDataModel::getLength(const std::string& expr) {
	if (!isDeclared(expr)) {
		throwErrorExecution("Variable " + expr + " was not declared");
	}

	if (!_variables[expr].hasKey("size")) {
		throwErrorExecution("Variable " + expr + " is no array");
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

	PromelaParser itemParser(item, PromelaParser::PROMELA_EXPR);
	PromelaParser arrayParser(ss.str(), PromelaParser::PROMELA_EXPR);

	setVariable(itemParser.ast, getVariable(arrayParser.ast));

	if (index.length() > 0) {
		PromelaParser indexParser(index, PromelaParser::PROMELA_EXPR);
		setVariable(indexParser.ast, iteration);
	}

}

void PromelaDataModel::eval(const Element<std::string>& scriptElem, const std::string& expr) {
	PromelaParser parser(expr, PromelaParser::PROMELA_STMNT);
	evaluateStmnt(parser.ast);
//	parser.dump();
}

bool PromelaDataModel::evalAsBool(const std::string& expr) {
	return evalAsBool(Arabica::DOM::Node<std::string>(), expr);
}

bool PromelaDataModel::evalAsBool(const Arabica::DOM::Node<std::string>& node, const std::string& expr) {
	PromelaParser parser(expr, PromelaParser::PROMELA_EXPR);
//	parser.dump();
	return evaluateExpr(parser.ast) > 0;
}

std::string PromelaDataModel::evalAsString(const std::string& expr) {
	if (isDeclared(expr)) {
		return Data::toJSON(_variables[expr]);
	}
	return expr;
}

void PromelaDataModel::assign(const Element<std::string>& assignElem,
                              const Node<std::string>& node,
                              const std::string& content) {
	PromelaParser parser(content, PromelaParser::PROMELA_DECL);
	evaluateDecl(parser.ast);
//	parser.dump();
//	std::cout << Data::toJSON(_variables) << std::endl;
}

void PromelaDataModel::evaluateDecl(void* ast) {
	PromelaParserNode* node = (PromelaParserNode*)ast;
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

				variable.compound["value"] = evaluateExpr(expr);

				assert(opIterAsgn == (*nameIter)->operands.end());
				_variables.compound[name->value] = variable;
			} else if ((*nameIter)->type == PML_VAR_ARRAY) {
				// variable arrays

				std::list<PromelaParserNode*>::iterator opIterAsgn = (*nameIter)->operands.begin();
				PromelaParserNode* name = *opIterAsgn++;
				int size = evaluateExpr(*opIterAsgn++);

				variable.compound["size"] = size;
				for (int i = 0; i < size; i++) {
					variable.compound["value"].array.push_back(Data(0, Data::INTERPRETED));
				}

				assert(opIterAsgn == (*nameIter)->operands.end());
				_variables.compound[name->value] = variable;

			} else {
				throwErrorExecution("Declaring variables via " + PromelaParserNode::typeToDesc((*nameIter)->type) + " not implemented");
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
		throwErrorExecution("Declaring variables via " + PromelaParserNode::typeToDesc(node->type) + " not implemented");
	}
}

int PromelaDataModel::evaluateExpr(void* ast) {
	PromelaParserNode* node = (PromelaParserNode*)ast;
	std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
	switch (node->type) {
	case PML_CONST:
		return strTo<int>(node->value);
	case PML_NAME:
	case PML_VAR_ARRAY:
		return getVariable(node);
	case PML_PLUS:
		return evaluateExpr(*opIter++) + evaluateExpr(*opIter++);
	case PML_MINUS:
		return evaluateExpr(*opIter++) - evaluateExpr(*opIter++);
	case PML_DIVIDE:
		return evaluateExpr(*opIter++) / evaluateExpr(*opIter++);
	case PML_MODULO:
		return evaluateExpr(*opIter++) % evaluateExpr(*opIter++);
	case PML_EQ:
		return evaluateExpr(*opIter++) == evaluateExpr(*opIter++);
	case PML_LT:
		return evaluateExpr(*opIter++) < evaluateExpr(*opIter++);
	case PML_LE:
		return evaluateExpr(*opIter++) <= evaluateExpr(*opIter++);
	case PML_GT:
		return evaluateExpr(*opIter++) > evaluateExpr(*opIter++);
	case PML_GE:
		return evaluateExpr(*opIter++) >= evaluateExpr(*opIter++);
	case PML_TIMES:
		return evaluateExpr(*opIter++) * evaluateExpr(*opIter++);
	case PML_LSHIFT:
		return evaluateExpr(*opIter++) << evaluateExpr(*opIter++);
	case PML_RSHIFT:
		return evaluateExpr(*opIter++) >> evaluateExpr(*opIter++);
	case PML_AND:
		return evaluateExpr(*opIter++) != 0 && evaluateExpr(*opIter++) != 0;
	case PML_OR:
		return evaluateExpr(*opIter++) != 0 || evaluateExpr(*opIter++) != 0;
	default:
		throwErrorExecution("Support for " + PromelaParserNode::typeToDesc(node->type) + " expressions not implemented");
	}
	return 0;
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
	default:
		throwErrorExecution("No support for " + PromelaParserNode::typeToDesc(node->type) + " statement implemented");
	}
}

void PromelaDataModel::setVariable(void* ast, int value) {
	PromelaParserNode* node = (PromelaParserNode*)ast;

	std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
	switch (node->type) {
	case PML_VAR_ARRAY: {
		PromelaParserNode* name = *opIter++;
		PromelaParserNode* expr = *opIter++;
		int index = evaluateExpr(expr);

		if (_variables.compound.find(name->value) == _variables.compound.end()) {
			throwErrorExecution("No variable " + name->value + " was declared");
		}

		if (!_variables[name->value].hasKey("size")) {
			throwErrorExecution("Variable " + name->value + " is no array");
		}

		if (strTo<int>(_variables[name->value]["size"].atom) <= index) {
			throwErrorExecution("Index " + toStr(index) + " in array " + name->value + "[" + _variables[name->value]["size"].atom + "] is out of bounds");
		}

		_variables.compound[name->value].compound["value"][index] = Data(value, Data::VERBATIM);

		break;
	}
	case PML_NAME:
		_variables.compound[node->value].compound["value"] = Data(value, Data::VERBATIM);
		break;
	default:
		break;
	}

//	std::cout << Data::toJSON(_variables) << std::endl;
}

int PromelaDataModel::getVariable(void* ast) {
	PromelaParserNode* node = (PromelaParserNode*)ast;
//	node->dump();

	std::list<PromelaParserNode*>::iterator opIter = node->operands.begin();
	switch(node->type) {
	case PML_NAME:
		if (_variables.compound.find(node->value) == _variables.compound.end()) {
			throwErrorExecution("No variable " + node->value + " was declared");
		}
		if (_variables[node->value].compound.find("size") != _variables[node->value].compound.end()) {
			throwErrorExecution("Type error: Variable " + node->value + " is an array");
		}
		return strTo<int>(_variables[node->value]["value"].atom);
	case PML_VAR_ARRAY: {
		PromelaParserNode* name = *opIter++;
		PromelaParserNode* expr = *opIter++;
		int index = evaluateExpr(expr);

		if (_variables.compound.find(name->value) == _variables.compound.end()) {
			throwErrorExecution("No variable " + name->value + " was declared");
		}

		if (!_variables[name->value].hasKey("size")) {
			throwErrorExecution("Variable " + name->value + " is no array");
		}

		if (strTo<int>(_variables[name->value]["size"].atom) <= index) {
			throwErrorExecution("Index " + toStr(index) + " in array " + name->value + "[" + _variables[name->value]["size"].atom + "] is out of bounds");
		}
		return strTo<int>(_variables.compound[name->value].compound["value"][index].atom);
	}
	default:
		throwErrorExecution("Retrieving value of " + PromelaParserNode::typeToDesc(node->type) + " variable not implemented");
	}
	return 0;
}

std::string PromelaDataModel::andExpressions(std::list<std::string> expressions) {

	if (expressions.size() == 0)
		return "";

	if (expressions.size() == 1)
		return *(expressions.begin());

	std::ostringstream exprSS;
	exprSS << "(";
	std::string conjunction = "";
	for (std::list<std::string>::const_iterator exprIter = expressions.begin();
	        exprIter != expressions.end();
	        exprIter++) {
		exprSS << conjunction << "(" << *exprIter << ")";
		conjunction = " && ";
	}
	exprSS << ")";
	return exprSS.str();
}

void PromelaDataModel::assign(const std::string& location, const Data& data) {
	// used for e.g. to assign command line parameters
	std::cout << "Ignoring " << location << " = " << Data::toJSON(data) << std::endl;
}

void PromelaDataModel::init(const Element<std::string>& dataElem,
                            const Node<std::string>& node,
                            const std::string& content) {
	// from <datamodel>
	assign(dataElem, node, content);
}
void PromelaDataModel::init(const std::string& location, const Data& data) {
	assign(location, data);
}

bool PromelaDataModel::isDeclared(const std::string& expr) {
	return _variables.compound.find(expr) != _variables.compound.end();
}


}
