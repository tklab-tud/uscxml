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

struct yy_buffer_state;
typedef yy_buffer_state *YY_BUFFER_STATE;
extern YY_BUFFER_STATE promela__scan_buffer(char *, size_t, void*);
void promela__delete_buffer(YY_BUFFER_STATE, void*);
YY_BUFFER_STATE promela__scan_string (const char * yystr , void*);


extern int promela_lex (PROMELA_STYPE* yylval_param, void* yyscanner);
int promela_lex_init (void**);
int promela_lex_destroy (void*);

void promela_error (uscxml::PromelaParser* ctx, void* yyscanner, const char* err) {
	// mark as pending exception as we cannot throw from constructor and have the destructor called
	uscxml::Event excEvent;
	excEvent.data.compound["exception"] = uscxml::Data(err, uscxml::Data::VERBATIM);
	excEvent.name = "error.execution";
	excEvent.eventType = uscxml::Event::PLATFORM;
	ctx->pendingException = excEvent;
}

namespace uscxml {

PromelaParser::PromelaParser(const std::string& expr) {
	init(expr);
}

PromelaParser::PromelaParser(const std::string& expr, Type expectedType) {
	init(expr);
	if (type != expectedType) {
		std::stringstream ss;
		ss << "Promela syntax type mismatch: Expected " << typeToDesc(expectedType) << " but got " << typeToDesc(type);

		uscxml::Event excEvent;
		excEvent.data.compound["exception"] = uscxml::Data(ss.str(), uscxml::Data::VERBATIM);
		excEvent.name = "error.execution";
		excEvent.eventType = uscxml::Event::PLATFORM;
		throw excEvent;
	}
}

void PromelaParser::init(const std::string& expr) {
	ast = NULL;
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
}

PromelaParserNode* PromelaParser::node(int type, int nrArgs, ...) {
	PromelaParserNode* newNode = new PromelaParserNode();
	newNode->type = type;
	va_list ap;
	va_start(ap, nrArgs);
	for(int i = 1; i <= nrArgs; i++) {
		newNode->operands.push_back(va_arg(ap, PromelaParserNode*));
	}
	return newNode;
}

PromelaParserNode* PromelaParser::value(int type, const char* value) {
	PromelaParserNode* newNode = new PromelaParserNode();
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
	}
	node->operands.clear();
}

void PromelaParserNode::push(PromelaParserNode* node) {
	operands.push_back(node);
}

void PromelaParserNode::dump(int indent) {
	std::string padding;
	for (int i = 0; i < indent; i++) {
		padding += "  ";
	}
	std::cout << padding << typeToDesc(type) << ": " << value << std::endl;
	for (std::list<PromelaParserNode*>::iterator iter = operands.begin();
	        iter != operands.end(); iter++) {
		(*iter)->dump(indent + 1);
	}
}

std::string PromelaParserNode::typeToDesc(int type) {
	switch(type) {
	case PLUS:
		return "PLUS";
	case MINUS:
		return "MINUS";
	case TIMES:
		return "TIMES";
	case DIVIDE:
		return "DIVIDE";
	case MODULO:
		return "MODULO";
	case BITAND:
		return "BITAND";
	case BITXOR:
		return "BITXOR";
	case BITOR:
		return "BITOR";
	case GT:
		return "GT";
	case LT:
		return "LT";
	case GE:
		return "GE";
	case LE:
		return "LE";
	case EQ:
		return "EQ";
	case NE:
		return "NE";
	case AND:
		return "AND";
	case OR:
		return "OR";
	case LSHIFT:
		return "LSHIFT";
	case RSHIFT:
		return "RSHIFT";
	case NEG:
		return "NEG";
	case ASGN:
		return "ASGN";
	case INCR:
		return "INCR";
	case DECR:
		return "DECR";
	case VAR_ARRAY:
		return "VAR_ARRAY";
	case DECL:
		return "DECL";
	case STMNT:
		return "STMNT";
	case TYPE:
		return "TYPE";
	case NAME:
		return "NAME";
	case CONST:
		return "CONST";
	case PRINT:
		return "PRINT";
	case SHOW:
		return "SHOW";
	case EXPR:
		return "EXPR";
	case VARLIST:
		return "VARLIST";
	case DECLLIST:
		return "DECLLIST";
	case NAMELIST:
		return "NAMELIST";

	default:
		return std::string("UNK(") + toStr(type) + ")";
	}
}

}