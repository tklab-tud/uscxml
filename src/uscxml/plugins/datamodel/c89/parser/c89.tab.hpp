/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

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

#ifndef YY_C89_C89_TAB_HPP_INCLUDED
# define YY_C89_C89_TAB_HPP_INCLUDED
/* Debug traces.  */
#ifndef C89_DEBUG
# if defined YYDEBUG
#if YYDEBUG
#   define C89_DEBUG 1
#  else
#   define C89_DEBUG 0
#  endif
# else /* ! defined YYDEBUG */
#  define C89_DEBUG 1
# endif /* ! defined YYDEBUG */
#endif  /* ! defined C89_DEBUG */
#if C89_DEBUG
extern int c89_debug;
#endif

/* Token type.  */
#ifndef C89_TOKENTYPE
# define C89_TOKENTYPE
  enum c89_tokentype
  {
    IDENTIFIER = 258,
    CONSTANT = 259,
    STRING_LITERAL = 260,
    SIZEOF = 261,
    PTR_OP = 262,
    INC_OP = 263,
    DEC_OP = 264,
    LEFT_OP = 265,
    RIGHT_OP = 266,
    LE_OP = 267,
    GE_OP = 268,
    EQ_OP = 269,
    NE_OP = 270,
    AND_OP = 271,
    OR_OP = 272,
    MUL_ASSIGN = 273,
    DIV_ASSIGN = 274,
    MOD_ASSIGN = 275,
    ADD_ASSIGN = 276,
    SUB_ASSIGN = 277,
    LEFT_ASSIGN = 278,
    RIGHT_ASSIGN = 279,
    AND_ASSIGN = 280,
    XOR_ASSIGN = 281,
    OR_ASSIGN = 282,
    TYPE_NAME = 283,
    TYPEDEF = 284,
    EXTERN = 285,
    STATIC = 286,
    AUTO = 287,
    REGISTER = 288,
    CHAR = 289,
    SHORT = 290,
    INT = 291,
    LONG = 292,
    SIGNED = 293,
    UNSIGNED = 294,
    FLOAT = 295,
    DOUBLE = 296,
    CONST = 297,
    VOLATILE = 298,
    VOID = 299,
    STRUCT = 300,
    UNION = 301,
    ENUM = 302,
    ELLIPSIS = 303,
    CASE = 304,
    DEFAULT = 305,
    IF = 306,
    ELSE = 307,
    SWITCH = 308,
    WHILE = 309,
    DO = 310,
    FOR = 311,
    GOTO = 312,
    CONTINUE = 313,
    BREAK = 314,
    RETURN = 315
  };
#endif

/* Value type.  */
#if ! defined C89_STYPE && ! defined C89_STYPE_IS_DECLARED

union C89_STYPE
{
#line 26 "c89.ypp" /* yacc.c:1909  */

  uscxml::C89ParserNode* node;
	char* value;

#line 128 "c89.tab.hpp" /* yacc.c:1909  */
};

typedef union C89_STYPE C89_STYPE;
# define C89_STYPE_IS_TRIVIAL 1
# define C89_STYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined C89_LTYPE && ! defined C89_LTYPE_IS_DECLARED
typedef struct C89_LTYPE C89_LTYPE;
struct C89_LTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define C89_LTYPE_IS_DECLARED 1
# define C89_LTYPE_IS_TRIVIAL 1
#endif



int c89_parse (uscxml::C89Parser* ctx, void * scanner);

#endif /* !YY_C89_C89_TAB_HPP_INCLUDED  */
