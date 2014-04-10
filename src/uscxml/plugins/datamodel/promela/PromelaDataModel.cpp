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

// #include "PromelaAssignParser.h"
//#include "PromelaExprParser.h"
// #include "PromelaStmntParser.h"
#include "PromelaParser.h"

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
	return dm;
}

void PromelaDataModel::registerIOProcessor(const std::string& name, const IOProcessor& ioprocessor) {
//	std::cout << "PromelaDataModel::registerIOProcessor" << std::endl;
}

void PromelaDataModel::setSessionId(const std::string& sessionId) {
//	std::cout << "PromelaDataModel::setSessionId" << std::endl;
	_sessionId = sessionId;
}

void PromelaDataModel::setName(const std::string& name) {
//	std::cout << "PromelaDataModel::setName" << std::endl;
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
	return expressionToAST(content);
}


bool PromelaDataModel::validate(const std::string& location, const std::string& schema) {
//	std::cout << "PromelaDataModel::validate" << std::endl;
	return true;
}

uint32_t PromelaDataModel::getLength(const std::string& expr) {
	return 0;
}

void PromelaDataModel::setForeach(const std::string& item,
                              const std::string& array,
                              const std::string& index,
                              uint32_t iteration) {
}

void PromelaDataModel::eval(const Element<std::string>& scriptElem, const std::string& expr) {
	expressionToAST(expr);
}

bool PromelaDataModel::evalAsBool(const std::string& expr) {
	return evalAsBool(Arabica::DOM::Node<std::string>(), expr);
}

bool PromelaDataModel::evalAsBool(const Arabica::DOM::Node<std::string>& node, const std::string& expr) {
	PromelaParser ast(expr);
//	std::cout << Data::toJSON(ast) << std::endl;
	return false;
	//	return evalAST(expressionToAST(expr));
}

Data PromelaDataModel::expressionToAST(const std::string& expr) {
	// see: http://en.wikipedia.org/wiki/Shunting-yard_algorithm (not used, prefix notation for now)
	Data ast;

	std::string tok_value;
	std::list<Token> tokens;
	size_t start = 0;

	for (int i = 0; i < expr.size();) {
		if (expr[i] == '(' || expr[i] == ')' || expr[i] == '!' || iswspace(expr[i]) || expr[i] == ',' || i + 1 == expr.size()) {
#if 0
			std::cout << ":" << expr << std::endl << ":";
			for (int c = 0; c < expr.size(); c++) {
				if (c == start) {
					std::cout << "s";
				} else if(c == i) {
					std::cout << "^";
				} else {
					std::cout << " ";
				}
			}
			std::cout << std::endl;;
#endif
			
			Token token;
			if (i > 0 && start < i - 1) {
				token.start = start;
				token.end = i;

				if (i + 1 == expr.size() && !(expr[i] == '(' || expr[i] == ')' || expr[i] == '!'))
					token.end++;
//				std::cout << expr.substr(token.start, token.end - token.start) << std::endl;

				tokens.push_back(token);
			}
			if (expr[i] == '(' || expr[i] == ')' || expr[i] == '!') {
				token.start = i;
				token.end = i + 1;
//				std::cout << expr.substr(token.start, token.end - token.start) << std::endl;

				tokens.push_back(token);
				i++;
			}
			if (expr[i] == ',') {
				i++;
			}
			if (i + 1 == expr.size())
				break;
			
			if (iswspace(expr[i])) {
				while(iswspace(expr[++i])); // skip remaining whitespaces
			}
			start = i;
		} else {
			i++;
		}
	}
	
	std::list<Data*> dataStack;
	std::list<Token> tokenStack;
	dataStack.push_back(&ast);

	for (std::list<Token>::iterator tokIter = tokens.begin();
			 tokIter != tokens.end();
			 tokIter++) {
		std::string token = expr.substr(tokIter->start, tokIter->end - tokIter->start);
//		std::cout << token << std::endl;

		if (false) {
		} else if (token == "(") {
			dataStack.back()->type = Data::INTERPRETED;
		} else if (token == ")") {
			dataStack.pop_back();
		} else if (token == "and") {
			dataStack.back()->array.push_back(Data("", Data::VERBATIM));
			dataStack.push_back(&(dataStack.back()->array.back().compound["and"]));
			dataStack.back()->type = Data::VERBATIM;
			continue;
		} else if (token == "or") {
			dataStack.back()->array.push_back(Data("", Data::VERBATIM));
			dataStack.push_back(&(dataStack.back()->array.back().compound["or"]));
			dataStack.back()->type = Data::VERBATIM;
			continue;
		} else if (token == "!" || token == "not") {
			dataStack.back()->array.push_back(Data("", Data::VERBATIM));
			dataStack.push_back(&(dataStack.back()->array.back().compound["not"]));
			dataStack.back()->type = Data::VERBATIM;
			continue;
		} else {
			// treat everything else as a variable
			dataStack.back()->array.push_back(Data(token, Data::VERBATIM));
		}

		// pop back if not bracketed
		while (dataStack.back()->type == Data::VERBATIM) {
			dataStack.pop_back();
		}

	}
	
//	std::cout << Data::toJSON(ast) << std::endl << std::endl;
	
	return ast;
}

bool PromelaDataModel::evalAST(const Data ast) {
	
#if 0
	std::cout << "===========" << std::endl;
	std::cout << Data::toJSON(ast) << std::endl;
	std::cout << "===========" << std::endl;
#endif
	
	// atomic term
	if (ast.atom.size() > 0) {
		// is it the event name? TODO: Use some prefix here!
		if (InterpreterImpl::nameMatch(ast.atom, _event.name))
			return true;

		if (_variables.find(ast.atom) != _variables.end()) {
			return _variables[ast.atom];
		}
		return false;
	}

	const std::list<Data>* arrayPtr = &(ast.array);

	// no operator is implied 'and'
	std::string op = "and";
	if (ast.compound.size() > 0) {
		op = ast.compound.begin()->first;
		arrayPtr = &(ast.compound.at(op).array);
	}
	
	for (std::list<Data>::const_iterator termIter = arrayPtr->begin();
			 termIter != arrayPtr->end();
			 termIter++) {
		bool result = evalAST(*termIter);
		if (false) {
		} else if (op == "and" && !result) {
			return false;
		} else if (op == "or" && result) {
			return true;
		} else if (op == "not" && result) {
			return false;
		}
	}
	return true;
}
	
std::string PromelaDataModel::evalAsString(const std::string& expr) {
	return "";
}

void PromelaDataModel::assign(const Element<std::string>& assignElem,
                          const Node<std::string>& node,
                          const std::string& content) {
	Data ast = expressionToAST(content);
	assign(true, ast);
}

void PromelaDataModel::assign(bool truth, Data ast) {
	for (std::list<Data>::iterator arrIter = ast.array.begin();
			 arrIter != ast.array.end();
			 arrIter++) {
		if (false) {
		} else if (arrIter->atom.size() > 0) {
			// simple atom to true
			_variables[arrIter->atom] = truth;
		} else if (arrIter->hasKey("not")) {
			// for convenience, we support bracketed "nots"
			assign(false, arrIter->compound["not"]);
		} else {
			Event exceptionEvent;
			exceptionEvent.data.compound["ast"] = ast;
			exceptionEvent.data.compound["exception"] = Data("Assignments can only contain atoms and negations", Data::VERBATIM);
			exceptionEvent.name = "error.execution";
			exceptionEvent.eventType = Event::PLATFORM;
			throw exceptionEvent;
		}
	}
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
	return _variables.find(expr) != _variables.end();
}


}
