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

#include "PromelaParser.h"
#include "parser/promela.tab.hpp"
#include "uscxml/messages/Event.h"

#include <iostream>

struct yy_buffer_state;
typedef yy_buffer_state *YY_BUFFER_STATE;
extern YY_BUFFER_STATE promela__scan_buffer(char *, size_t, void*);
void promela__delete_buffer(YY_BUFFER_STATE, void*);
YY_BUFFER_STATE promela__scan_string (const char * yystr , void*);


extern int promela_lex (PROMELA_STYPE* yylval_param, PROMELA_LTYPE* yylloc_param, void* yyscanner);
int promela_lex_init (void**);
int promela_lex_destroy (void*);

void promela_error (void* yylloc_param, uscxml::PromelaParser* ctx, void* yyscanner, const char* err) {
	PROMELA_LTYPE* yylloc = (PROMELA_LTYPE*)yylloc_param;
	// mark as pending exception as we cannot throw from constructor and have the destructor called
	ERROR_EXECUTION(excEvent, err);
	excEvent.data.compound["line"] = uscxml::Data(yylloc->first_line, uscxml::Data::VERBATIM);
	excEvent.data.compound["col"] = uscxml::Data(yylloc->first_column, uscxml::Data::VERBATIM);

	std::stringstream ssUnderline;
	for (int i = 0; i < yylloc->first_column; i++)
		ssUnderline << " ";
	ssUnderline << "^";
	excEvent.data.compound["sourcemark"] = uscxml::Data(ssUnderline.str(), uscxml::Data::VERBATIM);

	ctx->pendingException = excEvent;
}

namespace uscxml {

PromelaParser::PromelaParser(const std::string& expr) {
	init(expr);
}

PromelaParser::PromelaParser(const std::string& expr, int nrArgs, ...) {
	init(expr);

	if (nrArgs == 0)
		return;

	std::stringstream errSS;
	std::string seperator;
	errSS << "Promela syntax type mismatch: Expected {";

	va_list ap;
	va_start(ap, nrArgs);
	for(int i = 1; i <= nrArgs; i++) {
		int expectedType = va_arg(ap, int);
		if (type == expectedType)
			return;
		errSS << seperator << typeToDesc(expectedType);
		seperator = ", ";
	}
	errSS << "} but got " << typeToDesc(type);
	ERROR_EXECUTION_THROW(errSS.str());
}

void PromelaParser::init(const std::string& expr) {
	ast = NULL;
	parseInCompound = 0;
	input_length = expr.length() + 2;  // plus some zero terminators
	input = (char*) calloc(1, input_length);
	memcpy(input, expr.c_str(), expr.length());

	promela_lex_init(&scanner);
	//	promela_assign_set_extra(ast, &scanner);
	buffer = promela__scan_string(input, scanner);
	//	buffer = promela__scan_buffer(input, input_length, scanner);
	promela_parse(this, scanner);
	if (pendingException.name.size() > 0) {
		// parsing failed in promela_error
		destroy();
		pendingException.data.compound["sourceline"] = Data(expr, Data::VERBATIM);
		throw pendingException;
	}
}

void PromelaParser::destroy() {
	if (ast)
		delete(ast);
	free(input);
	promela__delete_buffer((YY_BUFFER_STATE)buffer, scanner);
	promela_lex_destroy(scanner);
}

PromelaParser::~PromelaParser() {
	destroy();
}

std::string PromelaParser::typeToDesc(int type) {
	switch (type) {
	case PROMELA_EXPR:
		return "expression";
	case PROMELA_DECL:
		return "declarations";
	case PROMELA_STMNT:
		return "statements";
	default:
		break;
	}
	return "";
}

PromelaParserNode::~PromelaParserNode() {
	while(operands.size() > 0) {
		delete operands.front();
		operands.pop_front();
	}
	if (loc)
		free(loc);
}

PromelaParserNode* PromelaParser::node(int type, int nrArgs, ...) {
	PromelaParserNode* newNode = new PromelaParserNode();
	
	newNode->type = type;
	va_list ap;
	va_start(ap, nrArgs);
	for(int i = 1; i <= nrArgs; i++) {
		newNode->operands.push_back(va_arg(ap, PromelaParserNode*));
		newNode->operands.back()->parent = newNode;
	}
	return newNode;
}

PromelaParserNode* PromelaParser::value(int type, void* location, const char* value) {
	PromelaParserNode* newNode = new PromelaParserNode();

	if (location) {
		PROMELA_LTYPE* location_param = (PROMELA_LTYPE*)location;
		newNode->loc = (PromelaParserNode::Location*)malloc(sizeof(PromelaParserNode::Location));
		newNode->loc->firstCol = location_param->first_column;
		newNode->loc->firstLine = location_param->first_line;
		newNode->loc->lastCol = location_param->last_column;
		newNode->loc->lastLine = location_param->last_line;
	}

	newNode->value = value;
	newNode->type = type;
	return newNode;
}

	
void PromelaParser::dump() {
	switch (type) {
	case PROMELA_EXPR:
		std::cout << "Promela Expression" << std::endl;
		break;
	case PROMELA_DECL:
		std::cout << "Promela Declarations" << std::endl;
		break;
	case PROMELA_STMNT:
		std::cout << "Promela Statement" << std::endl;
		break;
	}
	ast->dump();
}


void PromelaParserNode::merge(PromelaParserNode* node) {
	for (std::list<PromelaParserNode*>::iterator iter = node->operands.begin();
	        iter != node->operands.end(); iter++) {
		operands.push_back(*iter);
		(*iter)->parent = this;
	}
	node->operands.clear();
}

void PromelaParserNode::push(PromelaParserNode* node) {
	node->parent = this;
	operands.push_back(node);
}

void PromelaParserNode::dump(int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	std::cout << padding << typeToDesc(type) << ": " << value;
	if (loc != NULL) {
		std::cout << " (" << loc->firstLine << ":" << loc->firstCol << ")-(" << loc->lastLine << ":" << loc->lastCol << ")";
	}
	std::cout << std::endl;
	for (std::list<PromelaParserNode*>::iterator iter = operands.begin();
	        iter != operands.end(); iter++) {
		(*iter)->dump(indent + 1);
	}
}

std::string PromelaParserNode::typeToDesc(int type) {
	switch(type) {
	case PML_PLUS:
		return "PLUS";
	case PML_MINUS:
		return "MINUS";
	case PML_TIMES:
		return "TIMES";
	case PML_DIVIDE:
		return "DIVIDE";
	case PML_MODULO:
		return "MODULO";
	case PML_BITAND:
		return "BITAND";
	case PML_BITXOR:
		return "BITXOR";
	case PML_BITOR:
		return "BITOR";
	case PML_GT:
		return "GT";
	case PML_LT:
		return "LT";
	case PML_GE:
		return "GE";
	case PML_LE:
		return "LE";
	case PML_EQ:
		return "EQ";
	case PML_NE:
		return "NE";
	case PML_AND:
		return "AND";
	case PML_OR:
		return "OR";
	case PML_LSHIFT:
		return "LSHIFT";
	case PML_RSHIFT:
		return "RSHIFT";
	case PML_NEG:
		return "NEG";
	case PML_ASGN:
		return "ASGN";
	case PML_INCR:
		return "INCR";
	case PML_DECR:
		return "DECR";
	case PML_VAR_ARRAY:
		return "VAR_ARRAY";
	case PML_DECL:
		return "DECL";
	case PML_STMNT:
		return "STMNT";
	case PML_TYPE:
		return "TYPE";
	case PML_NAME:
		return "NAME";
	case PML_CONST:
		return "CONST";
	case PML_PRINT:
		return "PRINT";
	case PML_SHOW:
		return "SHOW";
	case PML_EXPR:
		return "EXPR";
	case PML_VARLIST:
		return "VARLIST";
	case PML_DECLLIST:
		return "DECLLIST";
	case PML_NAMELIST:
		return "NAMELIST";
	case PML_STRING:
		return "STRING";
	case PML_TYPEDEF:
		return "TYPEDEF";
	case PML_CMPND:
		return "CMPND";
	case PML_ASSERT:
		return "ASSERT";

	default:
		return std::string("UNK(") + toStr(type) + ")";
	}
}

}