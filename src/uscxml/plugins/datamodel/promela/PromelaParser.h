// bison -v -d promela-expr.ypp && flex promela-expr.l
// bison promela-expr.ypp && flex promela-expr.l

#ifndef PROMELA_H_9AB78YB1
#define PROMELA_H_9AB78YB1

#include <stdlib.h>
#include <stdarg.h>

#include "uscxml/Message.h"

#define GRAMMAR_COMMON(name, uc_name) \
struct yy_buffer_state; \
typedef yy_buffer_state *YY_BUFFER_STATE; \
extern YY_BUFFER_STATE promela_##name##__scan_buffer(char *, size_t, void*); \
extern int promela_##name##_lex (PROMELA_##uc_name##_STYPE* yylval_param, void* yyscanner); \
int promela_##name##_lex_init (void**); \
int promela_##name##_lex_destroy (void*); \

namespace uscxml {

class PromelaParser;
	
struct PromelaParserNode {
	PromelaParserNode() : type(0) {}
	int type;
	std::string value;
	std::list<PromelaParserNode*> operands;
	
	void merge(PromelaParserNode* node) {
		for (std::list<PromelaParserNode*>::iterator iter = node->operands.begin();
				 iter != node->operands.end(); iter++) {
			operands.push_back(*iter);
		}
	}

	void push(PromelaParserNode* node) {
		operands.push_back(node);
	}

	void dump(int indent = 0) {
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
	
	static std::string typeToDesc(int type);

};

class PromelaParser {
public:
	enum Type {
		PROMELA_EXPR,
		PROMELA_DECL,
		PROMELA_STMNT
	};
	
	static std::string typeToDesc(int type);

	PromelaParser(const std::string& expr, Type expectedType);
	virtual ~PromelaParser();
	
	virtual PromelaParserNode* node(int type, int nrArgs, ...) {
		PromelaParserNode* newNode = new PromelaParserNode();
		newNode->type = type;
		va_list ap;
    va_start(ap, nrArgs);
    for(int i = 1; i <= nrArgs; i++) {
			newNode->operands.push_back(va_arg(ap, PromelaParserNode*));
		}
		return newNode;
	}

	virtual PromelaParserNode* value(int type, const char* value) {
		PromelaParserNode* newNode = new PromelaParserNode();
		newNode->value = value;
		newNode->type = type;
		return newNode;
	}

	void dump() {
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
	
	PromelaParserNode* ast;
	Type type;

protected:
		
	void* scanner;
	char* input;
	size_t input_length;
};

}

void promela_error (uscxml::PromelaParser* ctx, void* yyscanner, const char* err);

#endif /* end of include guard: PROMELA_H_9AB78YB1 */
