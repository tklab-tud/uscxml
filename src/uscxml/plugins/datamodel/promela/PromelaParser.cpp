#include "PromelaParser.h"
#include "parser/promela.tab.hpp"

struct yy_buffer_state; \
typedef yy_buffer_state *YY_BUFFER_STATE; \
extern YY_BUFFER_STATE promela__scan_buffer(char *, size_t, void*); \
extern int promela_lex (PROMELA_STYPE* yylval_param, void* yyscanner); \
int promela_lex_init (void**); \
int promela_lex_destroy (void*); \

void promela_error (uscxml::PromelaParser* ctx, void* yyscanner, const char* err) {
	std::cout << err << std::endl;
}

namespace uscxml {

PromelaParser::PromelaParser(const std::string& expr) {
	input_length = expr.length() + 5;  // plus some zero terminators
	input = (char*) calloc(1, input_length);
	memcpy(input, expr.c_str(), expr.length());

	promela_lex_init(&scanner);
	//	promela_assign_set_extra(ast, &scanner);
	promela__scan_buffer(input, input_length, scanner);
	promela_parse(this, scanner);
}
PromelaParser::~PromelaParser() {
	free(input);
	promela_lex_destroy(scanner);
}

std::string PromelaParser::typeToDesc(int type) {
	switch(type) {
		case PLUS: return "PLUS";
		case MINUS: return "MINUS";
		case TIMES: return "TIMES";
		case DIVIDE: return "DIVIDE";
		case MODULO: return "MODULO";
		case BITAND: return "BITAND";
		case BITXOR: return "BITXOR";
		case BITOR: return "BITOR";
		case GT: return "GT";
		case LT: return "LT";
		case GE: return "GE";
		case LE: return "LE";
		case EQ: return "EQ";
		case NE: return "NE";
		case AND: return "AND";
		case OR: return "OR";
		case LSHIFT: return "LSHIFT";
		case RSHIFT: return "RSHIFT";
		case NEG: return "NEG";
		case ASGN: return "ASGN";
		default:
			return std::string("UNK(") + toStr(type) + ")";
	}
}

}