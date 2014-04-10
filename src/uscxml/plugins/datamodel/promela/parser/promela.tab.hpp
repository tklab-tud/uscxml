/* A Bison parser, made by GNU Bison 2.7.12-4996.  */

/* Bison interface for Yacc-like parsers in C
   
      Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_PROMELA_PROMELA_TAB_HPP_INCLUDED
# define YY_PROMELA_PROMELA_TAB_HPP_INCLUDED
/* Enabling traces.  */
#ifndef PROMELA_DEBUG
# if defined YYDEBUG
#  if YYDEBUG
#   define PROMELA_DEBUG 1
#  else
#   define PROMELA_DEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define PROMELA_DEBUG 1
# endif /* ! defined YYDEBUG */
#endif  /* ! defined PROMELA_DEBUG */
#if PROMELA_DEBUG
extern int promela_debug;
#endif

/* Tokens.  */
#ifndef PROMELA_TOKENTYPE
# define PROMELA_TOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum promela_tokentype {
     VAR_ARRAY = 258,
     VARLIST = 259,
     DECL = 260,
     DECLLIST = 261,
     STMNT = 262,
     COLON = 263,
     EXPR = 264,
     NAMELIST = 265,
     ASSERT = 266,
     PRINT = 267,
     PRINTM = 268,
     LEN = 269,
     STRING = 270,
     TYPEDEF = 271,
     MTYPE = 272,
     INLINE = 273,
     RETURN = 274,
     LABEL = 275,
     OF = 276,
     GOTO = 277,
     BREAK = 278,
     ELSE = 279,
     SEMI = 280,
     ARROW = 281,
     IF = 282,
     FI = 283,
     DO = 284,
     OD = 285,
     FOR = 286,
     SELECT = 287,
     IN = 288,
     SEP = 289,
     DOTDOT = 290,
     HIDDEN = 291,
     SHOW = 292,
     ISLOCAL = 293,
     CONST = 294,
     TYPE = 295,
     XU = 296,
     NAME = 297,
     UNAME = 298,
     PNAME = 299,
     INAME = 300,
     CLAIM = 301,
     TRACE = 302,
     INIT = 303,
     LTL = 304,
     COMMA = 305,
     ASGN = 306,
     AND = 307,
     OR = 308,
     BITAND = 309,
     BITXOR = 310,
     BITOR = 311,
     NE = 312,
     EQ = 313,
     LE = 314,
     GE = 315,
     LT = 316,
     GT = 317,
     RSHIFT = 318,
     LSHIFT = 319,
     MINUS = 320,
     PLUS = 321,
     MODULO = 322,
     DIVIDE = 323,
     TIMES = 324,
     DECR = 325,
     INCR = 326,
     COMPL = 327,
     NEG = 328,
     DOT = 329
   };
#endif


#if ! defined PROMELA_STYPE && ! defined PROMELA_STYPE_IS_DECLARED
typedef union PROMELA_STYPE
{
/* Line 2053 of yacc.c  */
#line 38 "promela.ypp"

  uscxml::PromelaParserNode* node;
	char* value;


/* Line 2053 of yacc.c  */
#line 145 "promela.tab.hpp"
} PROMELA_STYPE;
# define PROMELA_STYPE_IS_TRIVIAL 1
# define promela_stype PROMELA_STYPE /* obsolescent; will be withdrawn */
# define PROMELA_STYPE_IS_DECLARED 1
#endif


#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int promela_parse (void *YYPARSE_PARAM);
#else
int promela_parse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int promela_parse (uscxml::PromelaParser* ctx, void * scanner);
#else
int promela_parse ();
#endif
#endif /* ! YYPARSE_PARAM */

#endif /* !YY_PROMELA_PROMELA_TAB_HPP_INCLUDED  */
