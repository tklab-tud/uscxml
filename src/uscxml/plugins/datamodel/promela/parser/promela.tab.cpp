/* A Bison parser, made by GNU Bison 2.7.12-4996.  */

/* Bison implementation for Yacc-like parsers in C
   
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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.7.12-4996"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Substitute the type names.  */
#define YYSTYPE         PROMELA_STYPE
/* Substitute the variable and function names.  */
#define yyparse         promela_parse
#define yylex           promela_lex
#define yyerror         promela_error
#define yylval          promela_lval
#define yychar          promela_char
#define yydebug         promela_debug
#define yynerrs         promela_nerrs

/* Copy the first part of user declarations.  */
/* Line 371 of yacc.c  */
#line 14 "promela.ypp"

#include "../PromelaParser.h"
#include "promela.tab.hpp"
#include <sys/types.h>
#include <stdarg.h>

#define YYMAXDEPTH	20000	// default is 10000
#define YYDEBUG		1
#define YYERROR_VERBOSE 1

extern int promela_lex (PROMELA_STYPE* yylval_param, void* yyscanner);

using namespace uscxml;

/* Line 371 of yacc.c  */
#line 91 "promela.tab.cpp"

# ifndef YY_NULL
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULL nullptr
#  else
#   define YY_NULL 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "promela.tab.hpp".  */
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
     PML_DOT = 329
   };
#endif


#if ! defined PROMELA_STYPE && ! defined PROMELA_STYPE_IS_DECLARED
typedef union PROMELA_STYPE
{
/* Line 387 of yacc.c  */
#line 38 "promela.ypp"

  uscxml::PromelaParserNode* node;
	char* value;


/* Line 387 of yacc.c  */
#line 222 "promela.tab.cpp"
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

/* Copy the second part of user declarations.  */

/* Line 390 of yacc.c  */
#line 249 "promela.tab.cpp"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef __attribute__
/* This feature is available in gcc versions 2.5 and later.  */
# if (! defined __GNUC__ || __GNUC__ < 2 \
      || (__GNUC__ == 2 && __GNUC_MINOR__ < 5))
#  define __attribute__(Spec) /* empty */
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif


/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(N) (N)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined PROMELA_STYPE_IS_TRIVIAL && PROMELA_STYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (YYID (0))
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  33
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   304

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  81
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  23
/* YYNRULES -- Number of rules.  */
#define YYNRULES  83
/* YYNRULES -- Number of states.  */
#define YYNSTATES  146

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   329

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      11,    12,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    13,     2,    14,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    15,     2,    16,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    80
};

#if PROMELA_DEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     7,     9,    11,    13,    18,    19,
      23,    24,    27,    31,    35,    39,    43,    47,    51,    55,
      59,    63,    67,    71,    75,    79,    83,    87,    91,    95,
      99,   103,   106,   109,   114,   116,   118,   119,   121,   123,
     125,   129,   133,   140,   142,   145,   149,   151,   155,   157,
     161,   163,   167,   172,   174,   177,   181,   185,   189,   193,
     197,   201,   203,   206,   209,   211,   214,   218,   220,   224,
     227,   230,   236,   241,   246,   249,   251,   252,   261,   262,
     264,   265,   268,   270
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      82,     0,    -1,    91,    -1,    88,    -1,    97,    -1,    85,
      -1,    48,    -1,    48,    13,    88,    14,    -1,    -1,    84,
      86,    87,    -1,    -1,    80,    85,    -1,    11,    88,    12,
      -1,    88,    72,    88,    -1,    88,    71,    88,    -1,    88,
      75,    88,    -1,    88,    74,    88,    -1,    88,    73,    88,
      -1,    88,    60,    88,    -1,    88,    61,    88,    -1,    88,
      62,    88,    -1,    88,    68,    88,    -1,    88,    67,    88,
      -1,    88,    66,    88,    -1,    88,    65,    88,    -1,    88,
      64,    88,    -1,    88,    63,    88,    -1,    88,    58,    88,
      -1,    88,    59,    88,    -1,    88,    70,    88,    -1,    88,
      69,    88,    -1,    79,    88,    -1,    71,    88,    -1,    20,
      11,    83,    12,    -1,    83,    -1,    45,    -1,    -1,    42,
      -1,    43,    -1,    44,    -1,    89,    46,    92,    -1,    89,
      49,    92,    -1,    89,    46,    57,    15,    96,    16,    -1,
      90,    -1,    90,    31,    -1,    90,    31,    91,    -1,    93,
      -1,    93,    56,    92,    -1,    94,    -1,    94,    57,    88,
      -1,    48,    -1,    48,     8,    45,    -1,    48,    13,    95,
      14,    -1,    45,    -1,    71,    95,    -1,    11,    95,    12,
      -1,    95,    72,    95,    -1,    95,    71,    95,    -1,    95,
      75,    95,    -1,    95,    74,    95,    -1,    95,    73,    95,
      -1,    48,    -1,    96,    48,    -1,    96,    56,    -1,    98,
      -1,    98,    31,    -1,    98,    31,    97,    -1,    99,    -1,
      83,    57,    88,    -1,    83,    77,    -1,    83,    76,    -1,
      18,    11,    21,   102,    12,    -1,    19,    11,    83,    12,
      -1,    19,    11,    45,    12,    -1,    17,    88,    -1,    88,
      -1,    -1,    83,    57,    51,   100,    11,   101,    12,    99,
      -1,    -1,   103,    -1,    -1,    56,   103,    -1,    88,    -1,
      88,    56,   103,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] =
{
       0,    84,    84,    88,    92,    98,   101,   102,   105,   105,
     109,   110,   120,   121,   122,   123,   124,   125,   126,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,   139,   140,   142,   143,   144,   148,   149,   150,   151,
     154,   155,   156,   159,   160,   161,   171,   172,   175,   176,
     179,   180,   181,   184,   185,   186,   187,   188,   189,   190,
     191,   194,   195,   204,   207,   208,   209,   212,   215,   216,
     217,   218,   219,   220,   221,   222,   223,   223,   226,   227,
     230,   231,   234,   235
};
#endif

#if PROMELA_DEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "PML_VAR_ARRAY", "PML_VARLIST",
  "PML_DECL", "PML_DECLLIST", "PML_STMNT", "PML_COLON", "PML_EXPR",
  "PML_NAMELIST", "'('", "')'", "'['", "']'", "'{'", "'}'", "PML_ASSERT",
  "PML_PRINT", "PML_PRINTM", "PML_LEN", "PML_STRING", "PML_TYPEDEF",
  "PML_MTYPE", "PML_INLINE", "PML_RETURN", "PML_LABEL", "PML_OF",
  "PML_GOTO", "PML_BREAK", "PML_ELSE", "PML_SEMI", "PML_ARROW", "PML_IF",
  "PML_FI", "PML_DO", "PML_OD", "PML_FOR", "PML_SELECT", "PML_IN",
  "PML_SEP", "PML_DOTDOT", "PML_HIDDEN", "PML_SHOW", "PML_ISLOCAL",
  "PML_CONST", "PML_TYPE", "PML_XU", "PML_NAME", "PML_UNAME", "PML_PNAME",
  "PML_INAME", "PML_CLAIM", "PML_TRACE", "PML_INIT", "PML_LTL",
  "PML_COMMA", "PML_ASGN", "PML_AND", "PML_OR", "PML_BITAND", "PML_BITXOR",
  "PML_BITOR", "PML_NE", "PML_EQ", "PML_LE", "PML_GE", "PML_LT", "PML_GT",
  "PML_RSHIFT", "PML_LSHIFT", "PML_MINUS", "PML_PLUS", "PML_MODULO",
  "PML_DIVIDE", "PML_TIMES", "PML_DECR", "PML_INCR", "PML_COMPL",
  "PML_NEG", "PML_DOT", "$accept", "program", "varref", "pfld", "cmpnd",
  "$@1", "sfld", "expr", "vis", "one_decl", "decl_lst", "var_list", "ivar",
  "vardcl", "const_expr", "nlst", "stmnt_lst", "stmnt", "Stmnt", "$@2",
  "args", "prargs", "arg", YY_NULL
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,    40,    41,    91,    93,   123,   125,   266,   267,   268,
     269,   270,   271,   272,   273,   274,   275,   276,   277,   278,
     279,   280,   281,   282,   283,   284,   285,   286,   287,   288,
     289,   290,   291,   292,   293,   294,   295,   296,   297,   298,
     299,   300,   301,   302,   303,   304,   305,   306,   307,   308,
     309,   310,   311,   312,   313,   314,   315,   316,   317,   318,
     319,   320,   321,   322,   323,   324,   325,   326,   327,   328,
     329
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    81,    82,    82,    82,    83,    84,    84,    86,    85,
      87,    87,    88,    88,    88,    88,    88,    88,    88,    88,
      88,    88,    88,    88,    88,    88,    88,    88,    88,    88,
      88,    88,    88,    88,    88,    88,    89,    89,    89,    89,
      90,    90,    90,    91,    91,    91,    92,    92,    93,    93,
      94,    94,    94,    95,    95,    95,    95,    95,    95,    95,
      95,    96,    96,    96,    97,    97,    97,    98,    99,    99,
      99,    99,    99,    99,    99,    99,   100,    99,   101,   101,
     102,   102,   103,   103
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     1,     1,     4,     0,     3,
       0,     2,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     2,     2,     4,     1,     1,     0,     1,     1,     1,
       3,     3,     6,     1,     2,     3,     1,     3,     1,     3,
       1,     3,     4,     1,     2,     3,     3,     3,     3,     3,
       3,     1,     2,     2,     1,     2,     3,     1,     3,     2,
       2,     5,     4,     4,     2,     1,     0,     8,     0,     1,
       0,     2,     1,     3
};

/* YYDEFACT[STATE-NAME] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
      36,     0,     0,     0,     0,     0,    37,    38,    39,    35,
       6,     0,     0,     0,    34,     8,     5,     3,     0,    43,
       2,     4,    64,    67,    34,     0,    74,     0,     0,     0,
       0,    32,    31,     1,     0,    70,    69,    10,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    36,    65,
      12,    80,     0,     0,     0,     0,    76,    68,     0,     9,
      27,    28,    18,    19,    20,    26,    25,    24,    23,    22,
      21,    30,    29,    14,    13,    17,    16,    15,    50,     0,
      40,    46,    48,    41,    45,    75,    66,     0,     0,    73,
      72,    33,     7,     0,    11,     0,     0,     0,     0,     0,
      82,    81,    71,    78,    51,     0,    53,     0,     0,    61,
       0,    47,    49,     0,     0,    79,     0,    54,    52,     0,
       0,     0,     0,     0,    42,    62,    63,    83,     0,    55,
      57,    56,    60,    59,    58,    77
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
      -1,    13,    24,    15,    16,    37,    69,   110,    18,    19,
      20,    90,    91,    92,   118,   120,    21,    22,    23,   103,
     124,    98,   111
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -109
static const yytype_int16 yypact[] =
{
      46,    65,    65,    -5,     7,     9,  -109,  -109,  -109,  -109,
       8,    65,    65,    33,   -53,  -109,  -109,   155,   -36,     5,
    -109,  -109,     6,  -109,  -109,    87,   193,    54,   -29,    36,
      65,    -1,  -109,  -109,    60,  -109,  -109,    13,    65,    65,
      65,    65,    65,    65,    65,    65,    65,    65,    65,    65,
      65,    65,    65,    65,    65,    65,   -40,    38,    35,    50,
    -109,    25,    71,    75,    84,   110,  -109,   193,    36,  -109,
     209,   209,   222,   222,   222,   170,   170,   229,   229,   229,
     229,   -46,   -46,    -1,    -1,  -109,  -109,  -109,     1,    82,
    -109,    51,    49,  -109,  -109,   193,  -109,    65,   100,  -109,
    -109,  -109,  -109,   103,  -109,    70,    11,    68,    38,    65,
     136,  -109,  -109,    65,  -109,    11,  -109,    11,   116,  -109,
      44,  -109,   193,    65,   106,  -109,    92,    28,  -109,    11,
      11,    11,    11,    11,  -109,  -109,  -109,  -109,    50,  -109,
      28,    28,  -109,  -109,  -109,  -109
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
    -109,  -109,     3,  -109,    52,  -109,  -109,     0,  -109,  -109,
      61,   -50,  -109,  -109,   117,  -109,    63,  -109,   -15,  -109,
    -109,  -109,  -108
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -76
static const yytype_int16 yytable[] =
{
      17,    25,    26,    14,    34,   125,    27,    93,    88,   105,
      56,    31,    32,    57,   106,   137,    62,    89,    28,    10,
      29,    30,   115,    35,    36,    51,    52,    53,    54,    55,
      65,    63,    64,    33,    67,   -44,    58,    59,    70,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      82,    83,    84,    85,    86,    87,   116,     1,   121,    95,
     134,     1,    14,     2,     3,     4,     5,     2,     3,     4,
       5,     1,    53,    54,    55,    61,     1,     6,     7,     8,
       5,    97,   117,    99,    10,     5,    88,   100,     6,     7,
       8,     9,   135,    68,    10,     9,   101,   107,    10,    60,
     136,   131,   132,   133,   139,     9,   109,   108,    10,   122,
       9,    66,   112,    10,   113,   114,   119,    11,   138,    94,
     104,    11,    96,   145,   102,    12,     0,     0,     0,    12,
     128,    11,     0,     0,     0,     0,    11,     0,    95,    12,
       0,    14,     0,     0,    12,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,    55,   129,   130,   131,   132,   133,    38,    39,
      40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,    55,   -75,   129,   130,   131,
     132,   133,   123,     0,    38,    39,    40,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,     0,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,     0,   126,     0,   127,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,    55,   140,   141,   142,   143,
     144,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    49,    50,
      51,    52,    53,    54,    55
};

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-109)))

#define yytable_value_is_error(Yytable_value) \
  YYID (0)

static const yytype_int16 yycheck[] =
{
       0,     1,     2,     0,    57,   113,    11,    57,    48,     8,
      46,    11,    12,    49,    13,   123,    45,    57,    11,    48,
      11,    13,    11,    76,    77,    71,    72,    73,    74,    75,
      30,    28,    29,     0,    34,     0,    31,    31,    38,    39,
      40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    45,    11,   108,    59,
      16,    11,    59,    17,    18,    19,    20,    17,    18,    19,
      20,    11,    73,    74,    75,    21,    11,    42,    43,    44,
      20,    56,    71,    12,    48,    20,    48,    12,    42,    43,
      44,    45,    48,    80,    48,    45,    12,    15,    48,    12,
      56,    73,    74,    75,    12,    45,    57,    56,    48,   109,
      45,    51,    12,    48,    11,    45,    48,    71,    12,    58,
      68,    71,    59,   138,    14,    79,    -1,    -1,    -1,    79,
      14,    71,    -1,    -1,    -1,    -1,    71,    -1,   138,    79,
      -1,   138,    -1,    -1,    79,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    68,    69,    70,    71,    72,
      73,    74,    75,    71,    72,    73,    74,    75,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    71,    72,    73,    74,    75,    31,    71,    72,    73,
      74,    75,    56,    -1,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    75,    -1,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    -1,   115,    -1,   117,    65,    66,    67,    68,    69,
      70,    71,    72,    73,    74,    75,   129,   130,   131,   132,
     133,    58,    59,    60,    61,    62,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    75,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    69,    70,
      71,    72,    73,    74,    75
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    11,    17,    18,    19,    20,    42,    43,    44,    45,
      48,    71,    79,    82,    83,    84,    85,    88,    89,    90,
      91,    97,    98,    99,    83,    88,    88,    11,    11,    11,
      13,    88,    88,     0,    57,    76,    77,    86,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    71,    72,    73,    74,    75,    46,    49,    31,    31,
      12,    21,    45,    83,    83,    88,    51,    88,    80,    87,
      88,    88,    88,    88,    88,    88,    88,    88,    88,    88,
      88,    88,    88,    88,    88,    88,    88,    88,    48,    57,
      92,    93,    94,    92,    91,    88,    97,    56,   102,    12,
      12,    12,    14,   100,    85,     8,    13,    15,    56,    57,
      88,   103,    12,    11,    45,    11,    45,    71,    95,    48,
      96,    92,    88,    56,   101,   103,    95,    95,    14,    71,
      72,    73,    74,    75,    16,    48,    56,   103,    12,    12,
      95,    95,    95,    95,    95,    99
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  However,
   YYFAIL appears to be in use.  Nevertheless, it is formally deprecated
   in Bison 2.4.2's NEWS entry, where a plan to phase it out is
   discussed.  */

#define YYFAIL		goto yyerrlab
#if defined YYFAIL
  /* This is here to suppress warnings from the GCC cpp's
     -Wunused-macros.  Normally we don't worry about that warning, but
     some users do, and we want to make it easy for users to remove
     YYFAIL uses, which will produce warnings from Bison 2.5.  */
#endif

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (ctx, scanner, YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))

/* Error token number */
#define YYTERROR	1
#define YYERRCODE	256


/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */
#ifdef YYLEX_PARAM
# define YYLEX yylex (&yylval, YYLEX_PARAM)
#else
# define YYLEX yylex (&yylval, scanner)
#endif

/* Enable debugging if requested.  */
#if PROMELA_DEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value, ctx, scanner); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, uscxml::PromelaParser* ctx, void * scanner)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep, ctx, scanner)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    uscxml::PromelaParser* ctx;
    void * scanner;
#endif
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
  YYUSE (ctx);
  YYUSE (scanner);
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, uscxml::PromelaParser* ctx, void * scanner)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep, ctx, scanner)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    uscxml::PromelaParser* ctx;
    void * scanner;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep, ctx, scanner);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule, uscxml::PromelaParser* ctx, void * scanner)
#else
static void
yy_reduce_print (yyvsp, yyrule, ctx, scanner)
    YYSTYPE *yyvsp;
    int yyrule;
    uscxml::PromelaParser* ctx;
    void * scanner;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       , ctx, scanner);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule, ctx, scanner); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !PROMELA_DEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !PROMELA_DEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULL, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULL;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - Assume YYFAIL is not used.  It's too flawed to consider.  See
       <http://lists.gnu.org/archive/html/bison-patches/2009-12/msg00024.html>
       for details.  YYERROR is fine as it does not invoke this
       function.
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULL, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, uscxml::PromelaParser* ctx, void * scanner)
#else
static void
yydestruct (yymsg, yytype, yyvaluep, ctx, scanner)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
    uscxml::PromelaParser* ctx;
    void * scanner;
#endif
{
  YYUSE (yyvaluep);
  YYUSE (ctx);
  YYUSE (scanner);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YYUSE (yytype);
}




/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (uscxml::PromelaParser* ctx, void * scanner)
#else
int
yyparse (ctx, scanner)
    uscxml::PromelaParser* ctx;
    void * scanner;
#endif
#endif
{
/* The lookahead symbol.  */
int yychar;


#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
static YYSTYPE yyval_default;
# define YY_INITIAL_VALUE(Value) = Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval YY_INITIAL_VALUE(yyval_default);

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
/* Line 1787 of yacc.c  */
#line 84 "promela.ypp"
    { 
    ctx->ast = (yyvsp[(1) - (1)].node); 
    ctx->type = PromelaParser::PROMELA_DECL; 
  }
    break;

  case 3:
/* Line 1787 of yacc.c  */
#line 88 "promela.ypp"
    { 
    ctx->ast = (yyvsp[(1) - (1)].node); 
    ctx->type = PromelaParser::PROMELA_EXPR;
  }
    break;

  case 4:
/* Line 1787 of yacc.c  */
#line 92 "promela.ypp"
    { 
    ctx->ast = (yyvsp[(1) - (1)].node); 
    ctx->type = PromelaParser::PROMELA_STMNT;
  }
    break;

  case 5:
/* Line 1787 of yacc.c  */
#line 98 "promela.ypp"
    {}
    break;

  case 6:
/* Line 1787 of yacc.c  */
#line 101 "promela.ypp"
    { (yyval.node) = ctx->value(PML_NAME, (yyvsp[(1) - (1)].value)); free((yyvsp[(1) - (1)].value)); }
    break;

  case 7:
/* Line 1787 of yacc.c  */
#line 102 "promela.ypp"
    { (yyval.node) = ctx->node(PML_VAR_ARRAY, 2, ctx->value(PML_NAME, (yyvsp[(1) - (4)].value)), (yyvsp[(3) - (4)].node)); free((yyvsp[(1) - (4)].value)); }
    break;

  case 8:
/* Line 1787 of yacc.c  */
#line 105 "promela.ypp"
    {}
    break;

  case 9:
/* Line 1787 of yacc.c  */
#line 106 "promela.ypp"
    {}
    break;

  case 10:
/* Line 1787 of yacc.c  */
#line 109 "promela.ypp"
    {}
    break;

  case 11:
/* Line 1787 of yacc.c  */
#line 110 "promela.ypp"
    {}
    break;

  case 12:
/* Line 1787 of yacc.c  */
#line 120 "promela.ypp"
    { (yyval.node) = (yyvsp[(2) - (3)].node); }
    break;

  case 13:
/* Line 1787 of yacc.c  */
#line 121 "promela.ypp"
    { (yyval.node) = ctx->node(PML_PLUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 14:
/* Line 1787 of yacc.c  */
#line 122 "promela.ypp"
    { (yyval.node) = ctx->node(PML_MINUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 15:
/* Line 1787 of yacc.c  */
#line 123 "promela.ypp"
    { (yyval.node) = ctx->node(PML_TIMES, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 16:
/* Line 1787 of yacc.c  */
#line 124 "promela.ypp"
    { (yyval.node) = ctx->node(PML_DIVIDE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 17:
/* Line 1787 of yacc.c  */
#line 125 "promela.ypp"
    { (yyval.node) = ctx->node(PML_MODULO, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 18:
/* Line 1787 of yacc.c  */
#line 126 "promela.ypp"
    { (yyval.node) = ctx->node(PML_BITAND, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 19:
/* Line 1787 of yacc.c  */
#line 127 "promela.ypp"
    { (yyval.node) = ctx->node(PML_BITXOR, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 20:
/* Line 1787 of yacc.c  */
#line 128 "promela.ypp"
    { (yyval.node) = ctx->node(PML_BITOR, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 21:
/* Line 1787 of yacc.c  */
#line 129 "promela.ypp"
    { (yyval.node) = ctx->node(PML_GT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 22:
/* Line 1787 of yacc.c  */
#line 130 "promela.ypp"
    { (yyval.node) = ctx->node(PML_LT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 23:
/* Line 1787 of yacc.c  */
#line 131 "promela.ypp"
    { (yyval.node) = ctx->node(PML_GE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 24:
/* Line 1787 of yacc.c  */
#line 132 "promela.ypp"
    { (yyval.node) = ctx->node(PML_LE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 25:
/* Line 1787 of yacc.c  */
#line 133 "promela.ypp"
    { (yyval.node) = ctx->node(PML_EQ, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 26:
/* Line 1787 of yacc.c  */
#line 134 "promela.ypp"
    { (yyval.node) = ctx->node(PML_NE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 27:
/* Line 1787 of yacc.c  */
#line 135 "promela.ypp"
    { (yyval.node) = ctx->node(PML_AND, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 28:
/* Line 1787 of yacc.c  */
#line 136 "promela.ypp"
    { (yyval.node) = ctx->node(PML_OR, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 29:
/* Line 1787 of yacc.c  */
#line 137 "promela.ypp"
    { (yyval.node) = ctx->node(PML_LSHIFT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 30:
/* Line 1787 of yacc.c  */
#line 138 "promela.ypp"
    { (yyval.node) = ctx->node(PML_RSHIFT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 31:
/* Line 1787 of yacc.c  */
#line 139 "promela.ypp"
    { (yyval.node) = ctx->node(PML_NEG, 1, (yyvsp[(2) - (2)].node)); }
    break;

  case 32:
/* Line 1787 of yacc.c  */
#line 140 "promela.ypp"
    { (yyval.node) = ctx->node(PML_MINUS, 1, (yyvsp[(2) - (2)].node)); }
    break;

  case 33:
/* Line 1787 of yacc.c  */
#line 142 "promela.ypp"
    { (yyval.node) = ctx->node(PML_LEN, 1, (yyvsp[(3) - (4)].node));  }
    break;

  case 34:
/* Line 1787 of yacc.c  */
#line 143 "promela.ypp"
    {  }
    break;

  case 35:
/* Line 1787 of yacc.c  */
#line 144 "promela.ypp"
    { (yyval.node) = ctx->value(PML_CONST, (yyvsp[(1) - (1)].value)); free((yyvsp[(1) - (1)].value)); }
    break;

  case 36:
/* Line 1787 of yacc.c  */
#line 148 "promela.ypp"
    { (yyval.node) = ctx->node(PML_SHOW, 0); }
    break;

  case 37:
/* Line 1787 of yacc.c  */
#line 149 "promela.ypp"
    { (yyval.node) = ctx->node(PML_HIDDEN, 0); }
    break;

  case 38:
/* Line 1787 of yacc.c  */
#line 150 "promela.ypp"
    { (yyval.node) = ctx->node(PML_SHOW, 0); }
    break;

  case 39:
/* Line 1787 of yacc.c  */
#line 151 "promela.ypp"
    { (yyval.node) = ctx->node(PML_ISLOCAL, 0); }
    break;

  case 40:
/* Line 1787 of yacc.c  */
#line 154 "promela.ypp"
    { (yyval.node) = ctx->node(PML_DECL, 3, (yyvsp[(1) - (3)].node), ctx->value(PML_TYPE, (yyvsp[(2) - (3)].value)), (yyvsp[(3) - (3)].node)); free((yyvsp[(2) - (3)].value)); }
    break;

  case 41:
/* Line 1787 of yacc.c  */
#line 155 "promela.ypp"
    { (yyval.node) = ctx->node(PML_UNAME, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 42:
/* Line 1787 of yacc.c  */
#line 156 "promela.ypp"
    { (yyval.node) = ctx->node(PML_DECL, 3, (yyvsp[(1) - (6)].node), ctx->value(PML_TYPE, (yyvsp[(2) - (6)].value)), (yyvsp[(5) - (6)].node)); free((yyvsp[(2) - (6)].value)); }
    break;

  case 43:
/* Line 1787 of yacc.c  */
#line 159 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 44:
/* Line 1787 of yacc.c  */
#line 160 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (2)].node); }
    break;

  case 45:
/* Line 1787 of yacc.c  */
#line 161 "promela.ypp"
    {
    (yyval.node) = ctx->node(PML_DECLLIST, 1, (yyvsp[(1) - (3)].node));
    if((yyvsp[(3) - (3)].node)->type == PML_DECLLIST) {
      (yyval.node)->merge((yyvsp[(3) - (3)].node)); delete (yyvsp[(3) - (3)].node); 
    } else {
      (yyval.node)->push((yyvsp[(3) - (3)].node));
    }
  }
    break;

  case 46:
/* Line 1787 of yacc.c  */
#line 171 "promela.ypp"
    { (yyval.node) = ctx->node(PML_VARLIST, 1, (yyvsp[(1) - (1)].node)); }
    break;

  case 47:
/* Line 1787 of yacc.c  */
#line 172 "promela.ypp"
    { (yyval.node) = ctx->node(PML_VARLIST, 1, (yyvsp[(1) - (3)].node)); (yyval.node)->merge((yyvsp[(3) - (3)].node)); delete (yyvsp[(3) - (3)].node); }
    break;

  case 48:
/* Line 1787 of yacc.c  */
#line 175 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 49:
/* Line 1787 of yacc.c  */
#line 176 "promela.ypp"
    { (yyval.node) = ctx->node(PML_ASGN, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 50:
/* Line 1787 of yacc.c  */
#line 179 "promela.ypp"
    { (yyval.node) = ctx->value(PML_NAME, (yyvsp[(1) - (1)].value)); free((yyvsp[(1) - (1)].value)); }
    break;

  case 51:
/* Line 1787 of yacc.c  */
#line 180 "promela.ypp"
    { (yyval.node) = ctx->node(PML_COLON, 2, ctx->value(PML_NAME, (yyvsp[(1) - (3)].value)), ctx->value(PML_CONST, (yyvsp[(3) - (3)].value))); free((yyvsp[(1) - (3)].value)); free((yyvsp[(3) - (3)].value)); }
    break;

  case 52:
/* Line 1787 of yacc.c  */
#line 181 "promela.ypp"
    { (yyval.node) = ctx->node(PML_VAR_ARRAY, 2, ctx->value(PML_NAME, (yyvsp[(1) - (4)].value)), (yyvsp[(3) - (4)].node)); free((yyvsp[(1) - (4)].value)); }
    break;

  case 53:
/* Line 1787 of yacc.c  */
#line 184 "promela.ypp"
    { (yyval.node) = ctx->value(PML_CONST, (yyvsp[(1) - (1)].value)); free((yyvsp[(1) - (1)].value)); }
    break;

  case 54:
/* Line 1787 of yacc.c  */
#line 185 "promela.ypp"
    { (yyval.node) = ctx->node(PML_MINUS, 1, (yyvsp[(2) - (2)].node)); }
    break;

  case 55:
/* Line 1787 of yacc.c  */
#line 186 "promela.ypp"
    { (yyval.node) = (yyvsp[(2) - (3)].node); }
    break;

  case 56:
/* Line 1787 of yacc.c  */
#line 187 "promela.ypp"
    { (yyval.node) = ctx->node(PML_PLUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 57:
/* Line 1787 of yacc.c  */
#line 188 "promela.ypp"
    { (yyval.node) = ctx->node(PML_MINUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 58:
/* Line 1787 of yacc.c  */
#line 189 "promela.ypp"
    { (yyval.node) = ctx->node(PML_TIMES, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 59:
/* Line 1787 of yacc.c  */
#line 190 "promela.ypp"
    { (yyval.node) = ctx->node(PML_DIVIDE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 60:
/* Line 1787 of yacc.c  */
#line 191 "promela.ypp"
    { (yyval.node) = ctx->node(PML_MODULO, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 61:
/* Line 1787 of yacc.c  */
#line 194 "promela.ypp"
    { (yyval.node) = ctx->value(PML_NAME, (yyvsp[(1) - (1)].value)); free((yyvsp[(1) - (1)].value)); }
    break;

  case 62:
/* Line 1787 of yacc.c  */
#line 195 "promela.ypp"
    { 
    if ((yyvsp[(1) - (2)].node)->type == PML_NAME) {
      (yyval.node) = ctx->node(PML_NAMELIST, 1, (yyvsp[(1) - (2)].node));
      (yyval.node)->push(ctx->value(PML_NAME, (yyvsp[(2) - (2)].value)));
    } else {
      (yyvsp[(1) - (2)].node)->push(ctx->value(PML_NAME, (yyvsp[(2) - (2)].value)));
    }
    free((yyvsp[(2) - (2)].value));
  }
    break;

  case 63:
/* Line 1787 of yacc.c  */
#line 204 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (2)].node); }
    break;

  case 64:
/* Line 1787 of yacc.c  */
#line 207 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 65:
/* Line 1787 of yacc.c  */
#line 208 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (2)].node); }
    break;

  case 66:
/* Line 1787 of yacc.c  */
#line 209 "promela.ypp"
    { (yyval.node) = ctx->node(PML_STMNT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 67:
/* Line 1787 of yacc.c  */
#line 212 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 68:
/* Line 1787 of yacc.c  */
#line 215 "promela.ypp"
    { (yyval.node) = ctx->node(PML_ASGN, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;

  case 69:
/* Line 1787 of yacc.c  */
#line 216 "promela.ypp"
    { (yyval.node) = ctx->node(PML_INCR, 1, (yyvsp[(1) - (2)].node)); }
    break;

  case 70:
/* Line 1787 of yacc.c  */
#line 217 "promela.ypp"
    { (yyval.node) = ctx->node(PML_DECR, 1, (yyvsp[(1) - (2)].node)); }
    break;

  case 71:
/* Line 1787 of yacc.c  */
#line 218 "promela.ypp"
    { (yyval.node) = ctx->node(PML_PRINT, 2, ctx->value(PML_STRING, (yyvsp[(3) - (5)].value)), (yyvsp[(4) - (5)].node)); free((yyvsp[(3) - (5)].value)); }
    break;

  case 72:
/* Line 1787 of yacc.c  */
#line 219 "promela.ypp"
    { (yyval.node) = ctx->node(PML_PRINTM, 1, (yyvsp[(3) - (4)].node)); }
    break;

  case 73:
/* Line 1787 of yacc.c  */
#line 220 "promela.ypp"
    { (yyval.node) = ctx->node(PML_PRINTM, 1, ctx->value(PML_CONST, (yyvsp[(3) - (4)].value))); free((yyvsp[(3) - (4)].value)); }
    break;

  case 74:
/* Line 1787 of yacc.c  */
#line 221 "promela.ypp"
    {  }
    break;

  case 75:
/* Line 1787 of yacc.c  */
#line 222 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 76:
/* Line 1787 of yacc.c  */
#line 223 "promela.ypp"
    {  }
    break;

  case 77:
/* Line 1787 of yacc.c  */
#line 223 "promela.ypp"
    {  }
    break;

  case 78:
/* Line 1787 of yacc.c  */
#line 226 "promela.ypp"
    {  }
    break;

  case 79:
/* Line 1787 of yacc.c  */
#line 227 "promela.ypp"
    {  }
    break;

  case 80:
/* Line 1787 of yacc.c  */
#line 230 "promela.ypp"
    { (yyval.node) = ctx->value(0, ""); }
    break;

  case 81:
/* Line 1787 of yacc.c  */
#line 231 "promela.ypp"
    { (yyval.node) = (yyvsp[(2) - (2)].node); }
    break;

  case 82:
/* Line 1787 of yacc.c  */
#line 234 "promela.ypp"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 83:
/* Line 1787 of yacc.c  */
#line 235 "promela.ypp"
    { (yyval.node) = ctx->node(0, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node)); }
    break;


/* Line 1787 of yacc.c  */
#line 2162 "promela.tab.cpp"
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (ctx, scanner, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (ctx, scanner, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval, ctx, scanner);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp, ctx, scanner);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (ctx, scanner, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, ctx, scanner);
    }
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp, ctx, scanner);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}


/* Line 2050 of yacc.c  */
#line 239 "promela.ypp"


