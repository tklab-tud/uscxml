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
#  define PROMELA_DEBUG 0
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
     LBRACKET = 258,
     RBRACKET = 259,
     LEN = 260,
     TYPEDEF = 261,
     MTYPE = 262,
     INLINE = 263,
     RETURN = 264,
     LABEL = 265,
     OF = 266,
     GOTO = 267,
     BREAK = 268,
     ELSE = 269,
     SEMI = 270,
     ARROW = 271,
     IF = 272,
     FI = 273,
     DO = 274,
     OD = 275,
     FOR = 276,
     SELECT = 277,
     IN = 278,
     SEP = 279,
     DOTDOT = 280,
     HIDDEN = 281,
     SHOW = 282,
     ISLOCAL = 283,
     CONST = 284,
     TYPE = 285,
     XU = 286,
     NAME = 287,
     UNAME = 288,
     PNAME = 289,
     INAME = 290,
     STRING = 291,
     CLAIM = 292,
     TRACE = 293,
     INIT = 294,
     LTL = 295,
     ASGN = 296,
     AND = 297,
     OR = 298,
     BITAND = 299,
     BITXOR = 300,
     BITOR = 301,
     NE = 302,
     EQ = 303,
     LE = 304,
     GE = 305,
     LT = 306,
     GT = 307,
     RSHIFT = 308,
     LSHIFT = 309,
     MINUS = 310,
     PLUS = 311,
     MODULO = 312,
     DIVIDE = 313,
     TIMES = 314,
     COMPL = 315,
     NEG = 316,
     DOT = 317
   };
#endif


#if ! defined PROMELA_STYPE && ! defined PROMELA_STYPE_IS_DECLARED
typedef union PROMELA_STYPE
{
/* Line 2053 of yacc.c  */
#line 37 "promela.ypp"

  uscxml::PromelaParserNode* node;
	char* value;


/* Line 2053 of yacc.c  */
#line 133 "promela.tab.hpp"
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
