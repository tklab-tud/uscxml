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
     PML_VAR_ARRAY = 258,
     PML_VARLIST = 259,
     PML_DECL = 260,
     PML_DECLLIST = 261,
     PML_STMNT = 262,
     PML_COLON = 263,
     PML_EXPR = 264,
     PML_NAMELIST = 265,
     PML_ASSERT = 266,
     PML_PRINT = 267,
     PML_PRINTM = 268,
     PML_LEN = 269,
     PML_STRING = 270,
     PML_TYPEDEF = 271,
     PML_MTYPE = 272,
     PML_INLINE = 273,
     PML_RETURN = 274,
     PML_LABEL = 275,
     PML_OF = 276,
     PML_GOTO = 277,
     PML_BREAK = 278,
     PML_ELSE = 279,
     PML_SEMI = 280,
     PML_ARROW = 281,
     PML_IF = 282,
     PML_FI = 283,
     PML_DO = 284,
     PML_OD = 285,
     PML_FOR = 286,
     PML_SELECT = 287,
     PML_IN = 288,
     PML_SEP = 289,
     PML_DOTDOT = 290,
     PML_HIDDEN = 291,
     PML_SHOW = 292,
     PML_ISLOCAL = 293,
     PML_CONST = 294,
     PML_TYPE = 295,
     PML_XU = 296,
     PML_NAME = 297,
     PML_UNAME = 298,
     PML_PNAME = 299,
     PML_INAME = 300,
     PML_CLAIM = 301,
     PML_TRACE = 302,
     PML_INIT = 303,
     PML_LTL = 304,
     PML_COMMA = 305,
     PML_ASGN = 306,
     PML_AND = 307,
     PML_OR = 308,
     PML_BITAND = 309,
     PML_BITXOR = 310,
     PML_BITOR = 311,
     PML_NE = 312,
     PML_EQ = 313,
     PML_LE = 314,
     PML_GE = 315,
     PML_LT = 316,
     PML_GT = 317,
     PML_RSHIFT = 318,
     PML_LSHIFT = 319,
     PML_MINUS = 320,
     PML_PLUS = 321,
     PML_MODULO = 322,
     PML_DIVIDE = 323,
     PML_TIMES = 324,
     PML_DECR = 325,
     PML_INCR = 326,
     PML_COMPL = 327,
     PML_NEG = 328,
     PML_CMPND = 329,
     PML_DOT = 330
   };
#endif


#if ! defined PROMELA_STYPE && ! defined PROMELA_STYPE_IS_DECLARED
typedef union PROMELA_STYPE
{
/* Line 2053 of yacc.c  */
#line 39 "promela.ypp"

  uscxml::PromelaParserNode* node;
	char* value;


/* Line 2053 of yacc.c  */
#line 146 "promela.tab.hpp"
} PROMELA_STYPE;
# define PROMELA_STYPE_IS_TRIVIAL 1
# define promela_stype PROMELA_STYPE /* obsolescent; will be withdrawn */
# define PROMELA_STYPE_IS_DECLARED 1
#endif

#if ! defined PROMELA_LTYPE && ! defined PROMELA_LTYPE_IS_DECLARED
typedef struct PROMELA_LTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} PROMELA_LTYPE;
# define promela_ltype PROMELA_LTYPE /* obsolescent; will be withdrawn */
# define PROMELA_LTYPE_IS_DECLARED 1
# define PROMELA_LTYPE_IS_TRIVIAL 1
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
