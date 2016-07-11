/* see: http://www.phpcompiler.org/articles/reentrantparser.html */
/* see: http://spinroot.com/spin/Man/operators.html */

%option yylineno
%option reentrant
%option bison-bridge
%option prefix="c89_"
%option outfile="c89.lex.yy.cpp"
%option noyywrap
/*%option debug*/
%option never-interactive nounistd
%option bison-locations

%{
  
#include "../C89Parser.h"
#include "c89.tab.hpp"
#define YYSTYPE C89_STYPE
#define YYLTYPE C89_LTYPE
#define YY_USER_INIT \
  yycolumn = yylloc->first_line = yylloc->first_column = 0; \
  yylineno = yylloc->last_line = yylloc->last_column = 0; \

//int yycolumn = 1;

#define YY_USER_ACTION \
{ \
  yylloc->first_line = yylineno; \
  yylloc->first_column = yycolumn; \
  yylloc->last_column = yycolumn + yyleng; \
  yylloc->last_line = yylineno; \
  yycolumn = yycolumn + yyleng; \
}

%}

D			[0-9]
L			[a-zA-Z_]
H			[a-fA-F0-9]
E			[Ee][+-]?{D}+
FS			(f|F|l|L)
IS			(u|U|l|L)*

%{
#include <stdio.h>

int check_type()
{
/*	if (yytext == uint)
		return(TYPE_NAME);
*/
	return(IDENTIFIER);
}

%}

%%
\/\*([^*]|\*[^/])*\*+\/    /* multiline comments */
"//".*                     /* singlelien comments */
"#".*                     /* singlelien comments */

"auto"			{ return(AUTO); }
"break"			{ return(BREAK); }
"case"			{ return(CASE); }
"char"			{ return(CHAR); }
"const"			{ return(CONST); }
"continue"		{ return(CONTINUE); }
"default"		{ return(DEFAULT); }
"do"			{ return(DO); }
"double"		{ return(DOUBLE); }
"else"			{ return(ELSE); }
"enum"			{ return(ENUM); }
"extern"		{ return(EXTERN); }
"float"			{ return(FLOAT); }
"for"			{ return(FOR); }
"goto"			{ return(GOTO); }
"if"			{ return(IF); }
"int"			{ return(INT); }
"long"			{ return(LONG); }
"register"		{ return(REGISTER); }
"return"		{ return(RETURN); }
"short"			{ return(SHORT); }
"signed"		{ return(SIGNED); }
"sizeof"		{ return(SIZEOF); }
"static"		{ return(STATIC); }
"struct"		{ return(STRUCT); }
"switch"		{ return(SWITCH); }
"typedef"		{ return(TYPEDEF); }
"union"			{ return(UNION); }
"unsigned"		{ return(UNSIGNED); }
"void"			{ return(VOID); }
"volatile"		{ return(VOLATILE); }
"while"			{ return(WHILE); }

{L}({L}|{D})*		{ yylval->value = strdup(yytext); return(IDENTIFIER); }

0[xX]{H}+{IS}?		{ yylval->value = strdup(yytext); return(CONSTANT); }
0{D}+{IS}?		{ yylval->value = strdup(yytext); return(CONSTANT); }
{D}+{IS}?		{ yylval->value = strdup(yytext); return(CONSTANT); }
L?'(\\.|[^\\'])+'	{ yylval->value = strdup(yytext); return(CONSTANT); }

{D}+{E}{FS}?		{ yylval->value = strdup(yytext); return(CONSTANT); }
{D}*"."{D}+({E})?{FS}?	{ yylval->value = strdup(yytext); return(CONSTANT); }
{D}+"."{D}*({E})?{FS}?	{ yylval->value = strdup(yytext); return(CONSTANT); }

L?\"(\\.|[^\\"])*\"	{ yylval->value = strdup(yytext); return(STRING_LITERAL); }

"..."			{ return(ELLIPSIS); }
">>="			{ return(RIGHT_ASSIGN); }
"<<="			{ return(LEFT_ASSIGN); }
"+="			{ return(ADD_ASSIGN); }
"-="			{ return(SUB_ASSIGN); }
"*="			{ return(MUL_ASSIGN); }
"/="			{ return(DIV_ASSIGN); }
"%="			{ return(MOD_ASSIGN); }
"&="			{ return(AND_ASSIGN); }
"^="			{ return(XOR_ASSIGN); }
"|="			{ return(OR_ASSIGN); }
">>"			{ return(RIGHT_OP); }
"<<"			{ return(LEFT_OP); }
"++"			{ return(INC_OP); }
"--"			{ return(DEC_OP); }
"->"			{ return(PTR_OP); }
"&&"			{ return(AND_OP); }
"||"			{ return(OR_OP); }
"<="			{ return(LE_OP); }
">="			{ return(GE_OP); }
"=="			{ return(EQ_OP); }
"!="			{ return(NE_OP); }
";"			{ return(';'); }
("{"|"<%")		{ return('{'); }
("}"|"%>")		{ return('}'); }
","			{ return(','); }
":"			{ return(':'); }
"="			{ return('='); }
"("			{ return('('); }
")"			{ return(')'); }
("["|"<:")		{ return('['); }
("]"|":>")		{ return(']'); }
"."			{ return('.'); }
"&"			{ return('&'); }
"!"			{ return('!'); }
"~"			{ return('~'); }
"-"			{ return('-'); }
"+"			{ return('+'); }
"*"			{ return('*'); }
"/"			{ return('/'); }
"%"			{ return('%'); }
"<"			{ return('<'); }
">"			{ return('>'); }
"^"			{ return('^'); }
"|"			{ return('|'); }
"?"			{ return('?'); }

[ \t\v\n\f]		{ }
.			{ /* ignore bad characters */ }

%%
