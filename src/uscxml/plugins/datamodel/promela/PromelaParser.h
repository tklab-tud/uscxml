// bison -v -d promela-expr.ypp && flex promela-expr.l
// bison promela-expr.ypp && flex promela-expr.l

#ifndef PROMELA_H_9AB78YB1
#define PROMELA_H_9AB78YB1

#include <stdlib.h>
#include "uscxml/Message.h"

#define GRAMMAR_COMMON(name, uc_name) \
struct yy_buffer_state; \
typedef yy_buffer_state *YY_BUFFER_STATE; \
extern YY_BUFFER_STATE promela_##name##__scan_buffer(char *, size_t, void*); \
extern int promela_##name##_lex (PROMELA_##uc_name##_STYPE* yylval_param, void* yyscanner); \
int promela_##name##_lex_init (void**); \
int promela_##name##_lex_destroy (void*); \

namespace uscxml {

struct PromelaParserNode {
	PromelaParserNode() : type(0) {}
	int type;
	std::string value;
	std::list<PromelaParserNode*> operands;
};

class PromelaParser {
public:
	enum Type {
		PROMELA_EXPR,
		PROMELA_DECL,
		PROMELA_STMNT
	};
	
	PromelaParser(const std::string& expr);
	virtual ~PromelaParser();
	
	virtual PromelaParserNode* uniOp(int type, PromelaParserNode* oper) {
		PromelaParserNode* newNode = new PromelaParserNode();
		newNode->type = type;
		newNode->operands.push_back(oper);
		return newNode;
	}

	virtual PromelaParserNode* binOp(int type, PromelaParserNode* left, PromelaParserNode* right) {
		PromelaParserNode* newNode = new PromelaParserNode();
		newNode->type = type;
		newNode->operands.push_back(left);
		newNode->operands.push_back(right);
		return newNode;
	}

	virtual PromelaParserNode* value(const char* value) {
		PromelaParserNode* newNode = new PromelaParserNode();
		newNode->value = value;
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
		dump(ast);
	}
	
	void dump(PromelaParserNode* node, int indent = 0) {
		std::string padding;
		for (int i = 0; i < indent; i++) {
			padding += "  ";
		}
		std::cout << padding << typeToDesc(node->type) << ": " << node->value << std::endl;
		for (std::list<PromelaParserNode*>::iterator iter = node->operands.begin();
				 iter != node->operands.end(); iter++) {
			dump(*iter, indent + 1);
		}
	}

	virtual std::string typeToDesc(int type);

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
