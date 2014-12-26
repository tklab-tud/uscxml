/* see: http://www.phpcompiler.org/articles/reentrantparser.html */
/* see: http://spinroot.com/spin/Man/operators.html */


%option yylineno
%option reentrant
%option bison-bridge
%option prefix="promela_"
%option outfile="promela.lex.yy.cpp"
%option noyywrap
%option debug 
%option never-interactive nounistd
%option bison-locations

%{
  
#include "../PromelaParser.h"
#include "promela.tab.hpp"
#define YYSTYPE PROMELA_STYPE
#define YYLTYPE PROMELA_LTYPE
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

DIGIT    [0-9]
ID       [_a-zA-Z][_a-zA-Z0-9]*
L        [a-zA-Z_]

%%

\/\*([^*]|\*[^/])*\*+\/    /* multiline comments */

bit|bool|byte|int|mtype|short|unsigned|string|auto {
  yylval->value = strdup(yytext);
  return PML_TYPE;
}

len                        { return PML_LEN; }
false|skip|true            { yylval->value = strdup(yytext); return PML_CONST; }
printf                     { return PML_PRINT; }
typedef                    { return PML_TYPEDEF; }
assert                     { return PML_ASSERT; }

"!"                        { return PML_NEG; }
"~"                        { return PML_COMPL; }
"++"                       { return PML_INCR; }
"--"                       { return PML_DECR; }

"*"                        { return PML_TIMES; }
"/"                        { return PML_DIVIDE; }
"%"                        { return PML_MODULO; }

"+"                        { return PML_PLUS; }
"-"                        { return PML_MINUS; }

"<<"                       { return PML_LSHIFT; }
">>"                       { return PML_RSHIFT; }

"<="                       { return PML_LE; }
">="                       { return PML_GE; }
"<"                        { return PML_LT; }
">"                        { return PML_GT; }

"!="                       { return PML_NE; }
"=="                       { return PML_EQ; }

"&"                        { return PML_BITAND; }
"^"                        { return PML_BITXOR; }
"|"                        { return PML_BITOR; }


"&&"                       { return PML_AND; }
"||"                       { return PML_OR; }

"."                        { return PML_DOT; }
","                        { return PML_COMMA; }
";"                        { return PML_SEMI; }

"("                        { return '('; }
")"                        { return ')'; }

"["                        { return '['; }
"]"                        { return ']'; }

"{"                        { return '{'; }
"}"                        { return '}'; }

"="                        { return PML_ASGN; }

L?\"(\\.|[^\\"])*\"        { yylval->value = strdup(yytext); return(PML_STRING); }


L?'(\\.|[^\'])*\'          { 
  /* Non PROMELA extension for single quoted string literals */
  yylval->value = strdup(yytext); return(PML_STRING); 
} 

{DIGIT}+                   { yylval->value = strdup(yytext); return PML_CONST; }
{ID}                       { yylval->value = strdup(yytext); return PML_NAME; }

[ \t\n]+                   /* eat up whitespace */


.                          { /*printf( "Unrecognized character: %s\n", yytext ); */ }
