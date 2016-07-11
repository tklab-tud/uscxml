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

// bison -v c89.ypp && flex c89.l 

#ifndef C89PARSER_H_FE8E7C3E
#define C89PARSER_H_FE8E7C3E


#include <string>
#include <list>
#include <stdlib.h>
//#include <stdarg.h>
#include <cstdarg>

#include "uscxml/messages/Event.h"

namespace uscxml {

class C89Parser;

class C89ParserNode {
public:
	struct Location {
		int firstLine;
		int firstCol;
		int lastLine;
		int lastCol;
	};

	C89ParserNode() : type(0), parent(NULL), loc(NULL) {}
	virtual ~C89ParserNode();

	void merge(C89ParserNode* node);
	void push(C89ParserNode* node);
	void dump(int indent = 0);

	static std::string typeToDesc(int type);

	int type;
	std::string value;
	std::list<C89ParserNode*> operands;
	C89ParserNode* parent;
	Location* loc;
};

class C89Parser {
public:
	enum Type {
		C89_EXPR,
		C89_DECL,
		C89_STMNT
	};

	static std::string typeToDesc(int type);

	C89Parser() : ast(NULL) {}
	C89Parser(const std::string& expr);
	C89Parser(const std::string& expr, int nrArgs, ...);
	virtual ~C89Parser();

	virtual C89ParserNode* node(int type, int nrArgs, ...);
	virtual C89ParserNode* value(int type, void* location, const char* value);
	void dump();

	int parseInCompound;

	C89ParserNode* ast;
	Type type;

	Event pendingException;
	operator bool() const {
		return ast != NULL;
	}

protected:

	void init(const std::string& expr);
	void destroy();

	void* buffer;
	void* scanner;
	char* input;
	size_t input_length;
};

}

void c89_error (void* yylloc_param, uscxml::C89Parser* ctx, void* yyscanner, const char* err);

#endif /* end of include guard: C89PARSER_H_FE8E7C3E */
