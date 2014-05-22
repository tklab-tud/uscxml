/* see: http://www.phpcompiler.org/articles/reentrantparser.html */
/* see: http://spinroot.com/spin/Man/operators.html */


%option reentrant
%option bison-bridge
%option prefix="promela_"
%option outfile="promela.lex.yy.cpp"
%option noyywrap
%option debug 
%option never-interactive nounistd

%{
  
#include "../PromelaParser.h"
#include "promela.tab.hpp"
#define YYSTYPE PROMELA_STYPE

%}

DIGIT    [0-9]
ID       [_a-zA-Z][_a-zA-Z0-9]*
L        [a-zA-Z_]

%%

bit|bool|byte|int|mtype|short|unsigned {
  yylval->value = strdup(yytext);
  return PML_TYPE;
}

len                        { return PML_LEN; }
false|skip|true            { yylval->value = strdup(yytext); return PML_CONST; }
printf                     { return PML_PRINT; }
printm                     { return PML_PRINTM; }

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

L?\"(\\.|[^\\"])*\"         { yylval->value = strdup(yytext); return(PML_STRING); }

{DIGIT}+                   { yylval->value = strdup(yytext); return PML_CONST; }
{ID}                       { yylval->value = strdup(yytext); return PML_NAME; }

\'(\\.|[^'])*\'            { }

[ \t\n]+          /* eat up whitespace */

.                          { /*printf( "Unrecognized character: %s\n", yytext ); */ }
