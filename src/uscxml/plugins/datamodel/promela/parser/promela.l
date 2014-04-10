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
  return TYPE;
}

len                        { return LEN; }
false|skip|true            { yylval->value = strdup(yytext); return CONST; }
printf                     { return PRINT; }
printm                     { return PRINTM; }

"!"                        { return NEG; }
"~"                        { return COMPL; }
"++"                       { return INCR; }
"--"                       { return DECR; }

"*"                        { return TIMES; }
"/"                        { return DIVIDE; }
"%"                        { return MODULO; }

"+"                        { return PLUS; }
"-"                        { return MINUS; }

"<<"                       { return LSHIFT; }
">>"                       { return RSHIFT; }

"<="                       { return LE; }
">="                       { return GE; }
"<"                        { return LT; }
">"                        { return GT; }

"!="                       { return NE; }
"=="                       { return EQ; }

"&"                        { return BITAND; }
"^"                        { return BITXOR; }
"|"                        { return BITOR; }


"&&"                       { return AND; }
"||"                       { return OR; }

"."                        { return DOT; }
","                        { return COMMA; }
";"                        { return SEMI; }

"("                        { return '('; }
")"                        { return ')'; }

"["                        { return '['; }
"]"                        { return ']'; }

"{"                        { return '{'; }
"}"                        { return '}'; }

"="                        { return ASGN; }

L?\"(\\.|[^\\"])*\"         { yylval->value = strdup(yytext); return(STRING); }

{DIGIT}+                   { yylval->value = strdup(yytext); return CONST; }
{ID}                       { yylval->value = strdup(yytext); return NAME; }

\'(\\.|[^'])*\'            { }

[ \t\n]+          /* eat up whitespace */

.                          { /*printf( "Unrecognized character: %s\n", yytext ); */ }
