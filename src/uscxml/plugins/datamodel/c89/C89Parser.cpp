/**
 *  @file
 *  @author     2016 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
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

#include "C89Parser.h"
#include "parser/c89.tab.hpp"
#include "uscxml/messages/Event.h"

#include <cstring>
#include <iostream>
#include <cassert>

struct yy_buffer_state;
typedef yy_buffer_state *YY_BUFFER_STATE;
extern YY_BUFFER_STATE c89__scan_buffer(char *, size_t, void*);
void c89__delete_buffer(YY_BUFFER_STATE, void*);
YY_BUFFER_STATE c89__scan_string (const char * yystr , void*);


extern int c89_lex (C89_STYPE* yylval_param, C89_LTYPE* yylloc_param, void* yyscanner);
int c89_lex_init (void**);
int c89_lex_destroy (void*);

void c89_error (void* yylloc_param, uscxml::C89Parser* ctx, void* yyscanner, const char* err) {
	C89_LTYPE* yylloc = (C89_LTYPE*)yylloc_param;
	// mark as pending exception as we cannot throw from constructor and have the destructor called
	ERROR_EXECUTION(excEvent, err);
	excEvent.data.compound["line"] = uscxml::Data(yylloc->first_line, uscxml::Data::VERBATIM);
	excEvent.data.compound["col"] = uscxml::Data(yylloc->first_column, uscxml::Data::VERBATIM);

	std::stringstream ssUnderline;
	for (size_t i = 0; i < yylloc->first_column; i++)
		ssUnderline << " ";
	ssUnderline << "^";
	excEvent.data.compound["sourcemark"] = uscxml::Data(ssUnderline.str(), uscxml::Data::VERBATIM);

	ctx->pendingException = excEvent;
}

namespace uscxml {

C89Parser::C89Parser(const std::string& expr) {
	init(expr);
}

C89Parser::C89Parser(const std::string& expr, int nrArgs, ...) {
	init(expr);

	if (nrArgs == 0)
		return;

	std::stringstream errSS;
	std::string seperator;
	errSS << "C89 syntax type mismatch: Expected {";

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

void C89Parser::init(const std::string& expr) {
	ast = NULL;
	parseInCompound = 0;
	input_length = expr.length() + 2;  // plus some zero terminators
	input = (char*) calloc(1, input_length);
	memcpy(input, expr.c_str(), expr.length());

	c89_lex_init(&scanner);
	//	c89_assign_set_extra(ast, &scanner);
	buffer = c89__scan_string(input, scanner);
	//	buffer = c89__scan_buffer(input, input_length, scanner);
	c89_parse(this, scanner);
	if (pendingException.name.size() > 0) {
		// parsing failed in c89_error
		destroy();
		pendingException.data.compound["sourceline"] = Data(expr, Data::VERBATIM);
		throw pendingException;
	}
}

void C89Parser::destroy() {
	if (ast)
		delete(ast);
	free(input);
	c89__delete_buffer((YY_BUFFER_STATE)buffer, scanner);
	c89_lex_destroy(scanner);
}

C89Parser::~C89Parser() {
	destroy();
}

std::string C89Parser::typeToDesc(int type) {
	return "";
}

C89ParserNode::~C89ParserNode() {
	while(operands.size() > 0) {
		delete operands.front();
		operands.pop_front();
	}
	if (loc)
		free(loc);
}

C89ParserNode* C89Parser::node(int type, int nrArgs, ...) {
	C89ParserNode* newNode = new C89ParserNode();

	newNode->type = type;
	va_list ap;
	va_start(ap, nrArgs);
	for(int i = 1; i <= nrArgs; i++) {
        C89ParserNode* op = va_arg(ap, C89ParserNode*);
        assert(op != NULL);
        
		newNode->operands.push_back(op);
		newNode->operands.back()->parent = newNode;
	}
    
    this->ast = newNode;
	return newNode;
}

C89ParserNode* C89Parser::value(int type, void* location, const char* value) {
	C89ParserNode* newNode = new C89ParserNode();

	if (location) {
		C89_LTYPE* location_param = (C89_LTYPE*)location;
		newNode->loc = (C89ParserNode::Location*)malloc(sizeof(C89ParserNode::Location));
		newNode->loc->firstCol = location_param->first_column;
		newNode->loc->firstLine = location_param->first_line;
		newNode->loc->lastCol = location_param->last_column;
		newNode->loc->lastLine = location_param->last_line;
	}

    if (value != NULL) {
        newNode->value = value;
    }
	newNode->type = type;
    this->ast = newNode;
	return newNode;
}


void C89Parser::dump() {
	switch (type) {
	case C89_EXPR:
		std::cout << "C89 Expression" << std::endl;
		break;
	case C89_DECL:
		std::cout << "C89 Declarations" << std::endl;
		break;
	case C89_STMNT:
		std::cout << "C89 Statement" << std::endl;
		break;
	}
	ast->dump();
}


void C89ParserNode::merge(C89ParserNode* node) {
	for (std::list<C89ParserNode*>::iterator iter = node->operands.begin();
	        iter != node->operands.end(); iter++) {
		operands.push_back(*iter);
		(*iter)->parent = this;
	}
	node->operands.clear();
}

void C89ParserNode::push(C89ParserNode* node) {
	node->parent = this;
	operands.push_back(node);
}

void C89ParserNode::dump(int indent) {
	std::string padding;
	for (size_t i = 0; i < indent; i++) {
		padding += "  ";
	}
	std::cout << padding << typeToDesc(type) << ": " << value;
	if (loc != NULL) {
		std::cout << " (" << loc->firstLine << ":" << loc->firstCol << ")-(" << loc->lastLine << ":" << loc->lastCol << ")";
	}
	std::cout << std::endl;
	for (std::list<C89ParserNode*>::iterator iter = operands.begin();
	        iter != operands.end(); iter++) {
		(*iter)->dump(indent + 1);
	}
}

std::string C89ParserNode::typeToDesc(int type) {
    if (type < 256) {
        return std::string((char*)(&type), 1);
    }
    
    switch(type) {

	case IDENTIFIER: return "IDENTIFIER";
	case CONSTANT: return "CONSTANT";
	case STRING_LITERAL: return "STRING_LITERAL";
	case SIZEOF: return "SIZEOF";
	case PTR_OP: return "PTR_OP";
	case INC_OP: return "INC_OP";
	case DEC_OP: return "DEC_OP";
	case LEFT_OP: return "LEFT_OP";
	case RIGHT_OP: return "RIGHT_OP";
	case LE_OP: return "LE_OP";
	case GE_OP: return "GE_OP";
	case EQ_OP: return "EQ_OP";
	case NE_OP: return "NE_OP";
	case AND_OP: return "AND_OP";
	case OR_OP: return "OR_OP";
	case MUL_ASSIGN: return "MUL_ASSIGN";
	case DIV_ASSIGN: return "DIV_ASSIGN";
	case MOD_ASSIGN: return "MOD_ASSIGN";
	case ADD_ASSIGN: return "ADD_ASSIGN";
	case SUB_ASSIGN: return "SUB_ASSIGN";
	case LEFT_ASSIGN: return "LEFT_ASSIGN";
	case RIGHT_ASSIGN: return "RIGHT_ASSIGN";
	case AND_ASSIGN: return "AND_ASSIGN";
	case XOR_ASSIGN: return "XOR_ASSIGN";
	case OR_ASSIGN: return "OR_ASSIGN";
	case TYPE_NAME: return "TYPE_NAME";
	case TYPEDEF: return "TYPEDEF";
	case EXTERN: return "EXTERN";
	case STATIC: return "STATIC";
	case AUTO: return "AUTO";
	case REGISTER: return "REGISTER";
	case CHAR: return "CHAR";
	case SHORT: return "SHORT";
	case INT: return "INT";
	case LONG: return "LONG";
	case SIGNED: return "SIGNED";
	case UNSIGNED: return "UNSIGNED";
	case FLOAT: return "FLOAT";
	case DOUBLE: return "DOUBLE";
	case CONST: return "CONST";
	case VOLATILE: return "VOLATILE";
	case VOID: return "VOID";
	case STRUCT: return "STRUCT";
	case UNION: return "UNION";
	case ENUM: return "ENUM";
	case ELLIPSIS: return "ELLIPSIS";
	case CASE: return "CASE";
	case DEFAULT: return "DEFAULT";
	case IF: return "IF";
	case ELSE: return "ELSE";
	case SWITCH: return "SWITCH";
	case WHILE: return "WHILE";
	case DO: return "DO";
	case FOR: return "FOR";
	case GOTO: return "GOTO";
	case CONTINUE: return "CONTINUE";
	case BREAK: return "BREAK";
	case RETURN: return "RETURN";

	default:
		return std::string("UNK(") + toStr(type) + ")";
	}
}

}