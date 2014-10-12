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
	PML_CMPND = 329,
	PML_DOT = 330
};
#endif


#if ! defined PROMELA_STYPE && ! defined PROMELA_STYPE_IS_DECLARED
typedef union PROMELA_STYPE {
	/* Line 387 of yacc.c  */
#line 38 "promela.ypp"

	uscxml::PromelaParserNode* node;
	char* value;


	/* Line 387 of yacc.c  */
#line 223 "promela.tab.cpp"
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
#line 250 "promela.tab.cpp"

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
union yyalloc {
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
#define YYFINAL  34
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   311

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  82
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  23
/* YYNRULES -- Number of rules.  */
#define YYNRULES  85
/* YYNRULES -- Number of states.  */
#define YYNSTATES  152

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   330

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] = {
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
	71,    72,    73,    74,    75,    76,    77,    78,    79,    80,
	81
};

#if PROMELA_DEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] = {
	0,     0,     3,     5,     7,     9,    11,    13,    18,    21,
	22,    25,    29,    33,    37,    41,    45,    49,    53,    57,
	61,    65,    69,    73,    77,    81,    85,    89,    93,    97,
	101,   104,   107,   112,   114,   116,   118,   119,   121,   123,
	125,   129,   133,   140,   143,   149,   151,   154,   158,   160,
	164,   166,   170,   172,   176,   181,   183,   186,   190,   194,
	198,   202,   206,   210,   212,   215,   218,   220,   223,   227,
	229,   233,   236,   239,   245,   250,   255,   258,   260,   261,
	270,   271,   273,   274,   277,   279
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] = {
	83,     0,    -1,    92,    -1,    88,    -1,    98,    -1,    86,
	-1,    48,    -1,    48,    13,    88,    14,    -1,    85,    87,
	-1,    -1,    81,    86,    -1,    11,    88,    12,    -1,    88,
	72,    88,    -1,    88,    71,    88,    -1,    88,    75,    88,
	-1,    88,    74,    88,    -1,    88,    73,    88,    -1,    88,
	60,    88,    -1,    88,    61,    88,    -1,    88,    62,    88,
	-1,    88,    68,    88,    -1,    88,    67,    88,    -1,    88,
	66,    88,    -1,    88,    65,    88,    -1,    88,    64,    88,
	-1,    88,    63,    88,    -1,    88,    58,    88,    -1,    88,
	59,    88,    -1,    88,    70,    88,    -1,    88,    69,    88,
	-1,    79,    88,    -1,    71,    88,    -1,    20,    11,    84,
	12,    -1,    84,    -1,    45,    -1,    21,    -1,    -1,    42,
	-1,    43,    -1,    44,    -1,    89,    46,    93,    -1,    89,
	49,    93,    -1,    89,    46,    57,    15,    97,    16,    -1,
	89,    91,    -1,    22,    48,    15,    92,    16,    -1,    90,
	-1,    90,    31,    -1,    90,    31,    92,    -1,    94,    -1,
	94,    56,    93,    -1,    95,    -1,    95,    57,    88,    -1,
	48,    -1,    48,     8,    45,    -1,    48,    13,    96,    14,
	-1,    45,    -1,    71,    96,    -1,    11,    96,    12,    -1,
	96,    72,    96,    -1,    96,    71,    96,    -1,    96,    75,
	96,    -1,    96,    74,    96,    -1,    96,    73,    96,    -1,
	48,    -1,    97,    48,    -1,    97,    56,    -1,    99,    -1,
	99,    31,    -1,    99,    31,    98,    -1,   100,    -1,    84,
	57,    88,    -1,    84,    77,    -1,    84,    76,    -1,    18,
	11,    21,   103,    12,    -1,    19,    11,    84,    12,    -1,
	19,    11,    45,    12,    -1,    17,    88,    -1,    88,    -1,
	-1,    84,    57,    51,   101,    11,   102,    12,   100,    -1,
	-1,   104,    -1,    -1,    56,   104,    -1,    88,    -1,    88,
	56,   104,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] = {
	0,    84,    84,    88,    92,    98,   101,   102,   105,   132,
	133,   143,   144,   145,   146,   147,   148,   149,   150,   151,
	152,   153,   154,   155,   156,   157,   158,   159,   160,   161,
	162,   163,   165,   166,   167,   168,   174,   175,   176,   177,
	180,   181,   182,   183,   186,   189,   190,   191,   201,   202,
	205,   206,   209,   210,   211,   214,   215,   216,   217,   218,
	219,   220,   221,   224,   225,   234,   237,   238,   239,   242,
	245,   246,   247,   248,   249,   250,   251,   252,   253,   253,
	256,   257,   260,   261,   264,   265
};
#endif

#if PROMELA_DEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] = {
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
	"PML_NEG", "PML_CMPND", "PML_DOT", "$accept", "program", "varref",
	"pfld", "cmpnd", "sfld", "expr", "vis", "one_decl", "utype", "decl_lst",
	"var_list", "ivar", "vardcl", "const_expr", "nlst", "stmnt_lst", "stmnt",
	"Stmnt", "$@1", "args", "prargs", "arg", YY_NULL
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] = {
	0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
	265,    40,    41,    91,    93,   123,   125,   266,   267,   268,
	269,   270,   271,   272,   273,   274,   275,   276,   277,   278,
	279,   280,   281,   282,   283,   284,   285,   286,   287,   288,
	289,   290,   291,   292,   293,   294,   295,   296,   297,   298,
	299,   300,   301,   302,   303,   304,   305,   306,   307,   308,
	309,   310,   311,   312,   313,   314,   315,   316,   317,   318,
	319,   320,   321,   322,   323,   324,   325,   326,   327,   328,
	329,   330
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] = {
	0,    82,    83,    83,    83,    84,    85,    85,    86,    87,
	87,    88,    88,    88,    88,    88,    88,    88,    88,    88,
	88,    88,    88,    88,    88,    88,    88,    88,    88,    88,
	88,    88,    88,    88,    88,    88,    89,    89,    89,    89,
	90,    90,    90,    90,    91,    92,    92,    92,    93,    93,
	94,    94,    95,    95,    95,    96,    96,    96,    96,    96,
	96,    96,    96,    97,    97,    97,    98,    98,    98,    99,
	100,   100,   100,   100,   100,   100,   100,   100,   101,   100,
	102,   102,   103,   103,   104,   104
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] = {
	0,     2,     1,     1,     1,     1,     1,     4,     2,     0,
	2,     3,     3,     3,     3,     3,     3,     3,     3,     3,
	3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
	2,     2,     4,     1,     1,     1,     0,     1,     1,     1,
	3,     3,     6,     2,     5,     1,     2,     3,     1,     3,
	1,     3,     1,     3,     4,     1,     2,     3,     3,     3,
	3,     3,     3,     1,     2,     2,     1,     2,     3,     1,
	3,     2,     2,     5,     4,     4,     2,     1,     0,     8,
	0,     1,     0,     2,     1,     3
};

/* YYDEFACT[STATE-NAME] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] = {
	36,     0,     0,     0,     0,     0,    35,    37,    38,    39,
	34,     6,     0,     0,     0,    33,     9,     5,     3,     0,
	45,     2,     4,    66,    69,    33,     0,    76,     0,     0,
	0,     0,    31,    30,     1,     0,    72,    71,     0,     8,
	0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
	0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
	0,    43,    36,    67,    11,    82,     0,     0,     0,     0,
	78,    70,    10,    26,    27,    17,    18,    19,    25,    24,
	23,    22,    21,    20,    29,    28,    13,    12,    16,    15,
	14,     0,    52,     0,    40,    48,    50,    41,    47,    77,
	68,     0,     0,    75,    74,    32,     7,     0,    36,     0,
	0,     0,     0,     0,    84,    83,    73,    80,     0,    53,
	0,    55,     0,     0,    63,     0,    49,    51,     0,     0,
	81,    44,     0,    56,    54,     0,     0,     0,     0,     0,
	42,    64,    65,    85,     0,    57,    59,    58,    62,    61,
	60,    79
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] = {
	-1,    14,    25,    16,    17,    39,   114,    19,    20,    61,
	21,    94,    95,    96,   123,   125,    22,    23,    24,   107,
	129,   102,   115
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -112
static const yytype_int16 yypact[] = {
	50,    66,    66,     5,     8,    25,  -112,  -112,  -112,  -112,
	-112,    26,    66,    66,    62,   -52,    -8,  -112,   159,   -12,
	45,  -112,  -112,    57,  -112,  -112,    91,   200,    70,   -37,
	41,    66,    10,  -112,  -112,    54,  -112,  -112,    41,  -112,
	66,    66,    66,    66,    66,    66,    66,    66,    66,    66,
	66,    66,    66,    66,    66,    66,    66,    66,    48,   -39,
	49,  -112,   193,    61,  -112,    51,    88,    89,    92,   114,
	-112,   200,  -112,   216,   216,   229,   229,   229,   133,   133,
	236,   236,   236,   236,   -45,   -45,    10,    10,  -112,  -112,
	-112,    95,     7,    97,  -112,    64,    67,  -112,  -112,   200,
	-112,    66,   111,  -112,  -112,  -112,  -112,   115,   -21,    82,
	-7,    83,    49,    66,   182,  -112,  -112,    66,   118,  -112,
	-7,  -112,    -7,    44,  -112,    74,  -112,   200,    66,   123,
	-112,  -112,    96,    68,  -112,    -7,    -7,    -7,    -7,    -7,
	-112,  -112,  -112,  -112,    61,  -112,    68,    68,  -112,  -112,
	-112,  -112
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] = {
	-112,  -112,     3,  -112,    98,  -112,     0,  -112,  -112,  -112,
	-48,   -53,  -112,  -112,    75,  -112,    76,  -112,    -6,  -112,
	-112,  -112,  -111
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -78
static const yytype_int16 yytable[] = {
	18,    26,    27,    15,   120,    35,   130,    97,    66,    92,
	58,    11,    32,    33,    98,   109,    28,   143,    93,    29,
	110,     7,     8,     9,    36,    37,    53,    54,    55,    56,
	57,    69,    67,    68,    59,    71,    30,    60,   121,    31,
	73,    74,    75,    76,    77,    78,    79,    80,    81,    82,
	83,    84,    85,    86,    87,    88,    89,    90,   134,   126,
	118,     1,    34,    99,   122,     1,    15,     2,     3,     4,
	5,     6,     1,    38,     5,     6,    62,     1,     2,     3,
	4,     5,     6,    55,    56,    57,     5,     6,    63,    11,
	140,    65,     7,     8,     9,    10,    91,    92,    11,    10,
	103,   104,    11,    64,   105,    70,    10,   101,   145,    11,
	108,    10,   111,   127,    11,   135,   136,   137,   138,   139,
	112,    12,   141,   116,   113,    12,   117,   119,   106,    13,
	142,   124,    12,    13,   131,   144,    72,    12,   151,   100,
	13,   137,   138,   139,    99,    13,     0,    15,     0,    40,
	41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
	51,    52,    53,    54,    55,    56,    57,   135,   136,   137,
	138,   139,    40,    41,    42,    43,    44,    45,    46,    47,
	48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
	-77,     0,     0,   -46,     0,   132,     0,   133,    47,    48,
	49,    50,    51,    52,    53,    54,    55,    56,    57,   -46,
	146,   147,   148,   149,   150,     0,     0,    40,    41,    42,
	43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
	53,    54,    55,    56,    57,     7,     8,     9,   128,     0,
	40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
	50,    51,    52,    53,    54,    55,    56,    57,    40,    41,
	42,    43,    44,    45,    46,    47,    48,    49,    50,    51,
	52,    53,    54,    55,    56,    57,    42,    43,    44,    45,
	46,    47,    48,    49,    50,    51,    52,    53,    54,    55,
	56,    57,    45,    46,    47,    48,    49,    50,    51,    52,
	53,    54,    55,    56,    57,    51,    52,    53,    54,    55,
	56,    57
};

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-112)))

#define yytable_value_is_error(Yytable_value) \
  YYID (0)

static const yytype_int16 yycheck[] = {
	0,     1,     2,     0,    11,    57,   117,    60,    45,    48,
	22,    48,    12,    13,    62,     8,    11,   128,    57,    11,
	13,    42,    43,    44,    76,    77,    71,    72,    73,    74,
	75,    31,    29,    30,    46,    35,    11,    49,    45,    13,
	40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
	50,    51,    52,    53,    54,    55,    56,    57,    14,   112,
	108,    11,     0,    63,    71,    11,    63,    17,    18,    19,
	20,    21,    11,    81,    20,    21,    31,    11,    17,    18,
	19,    20,    21,    73,    74,    75,    20,    21,    31,    48,
	16,    21,    42,    43,    44,    45,    48,    48,    48,    45,
	12,    12,    48,    12,    12,    51,    45,    56,    12,    48,
	15,    45,    15,   113,    48,    71,    72,    73,    74,    75,
	56,    71,    48,    12,    57,    71,    11,    45,    14,    79,
	56,    48,    71,    79,    16,    12,    38,    71,   144,    63,
	79,    73,    74,    75,   144,    79,    -1,   144,    -1,    58,
	59,    60,    61,    62,    63,    64,    65,    66,    67,    68,
	69,    70,    71,    72,    73,    74,    75,    71,    72,    73,
	74,    75,    58,    59,    60,    61,    62,    63,    64,    65,
	66,    67,    68,    69,    70,    71,    72,    73,    74,    75,
	31,    -1,    -1,     0,    -1,   120,    -1,   122,    65,    66,
	67,    68,    69,    70,    71,    72,    73,    74,    75,    16,
	135,   136,   137,   138,   139,    -1,    -1,    58,    59,    60,
	61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
	71,    72,    73,    74,    75,    42,    43,    44,    56,    -1,
	58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
	68,    69,    70,    71,    72,    73,    74,    75,    58,    59,
	60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
	70,    71,    72,    73,    74,    75,    60,    61,    62,    63,
	64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
	74,    75,    63,    64,    65,    66,    67,    68,    69,    70,
	71,    72,    73,    74,    75,    69,    70,    71,    72,    73,
	74,    75
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] = {
	0,    11,    17,    18,    19,    20,    21,    42,    43,    44,
	45,    48,    71,    79,    83,    84,    85,    86,    88,    89,
	90,    92,    98,    99,   100,    84,    88,    88,    11,    11,
	11,    13,    88,    88,     0,    57,    76,    77,    81,    87,
	58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
	68,    69,    70,    71,    72,    73,    74,    75,    22,    46,
	49,    91,    31,    31,    12,    21,    45,    84,    84,    88,
	51,    88,    86,    88,    88,    88,    88,    88,    88,    88,
	88,    88,    88,    88,    88,    88,    88,    88,    88,    88,
	88,    48,    48,    57,    93,    94,    95,    93,    92,    88,
	98,    56,   103,    12,    12,    12,    14,   101,    15,     8,
	13,    15,    56,    57,    88,   104,    12,    11,    92,    45,
	11,    45,    71,    96,    48,    97,    93,    88,    56,   102,
	104,    16,    96,    96,    14,    71,    72,    73,    74,    75,
	16,    48,    56,   104,    12,    12,    96,    96,    96,    96,
	96,   100
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
	for (; yybottom <= yytop; yybottom++) {
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
	for (yyi = 0; yyi < yynrhs; yyi++) {
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
yytnamerr (char *yyres, const char *yystr) {
	if (*yystr == '"') {
		YYSIZE_T yyn = 0;
		char const *yyp = yystr;

		for (;;)
			switch (*++yyp) {
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
do_not_strip_quotes:
		;
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
                yytype_int16 *yyssp, int yytoken) {
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
	if (yytoken != YYEMPTY) {
		int yyn = yypact[*yyssp];
		yyarg[yycount++] = yytname[yytoken];
		if (!yypact_value_is_default (yyn)) {
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
				        && !yytable_value_is_error (yytable[yyx + yyn])) {
					if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM) {
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

	switch (yycount) {
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

	if (*yymsg_alloc < yysize) {
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
			if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount) {
				yyp += yytnamerr (yyp, yyarg[yyi++]);
				yyformat += 2;
			} else {
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

	if (yyss + yystacksize - 1 <= yyssp) {
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
	if (yychar == YYEMPTY) {
		YYDPRINTF ((stderr, "Reading a token: "));
		yychar = YYLEX;
	}

	if (yychar <= YYEOF) {
		yychar = yytoken = YYEOF;
		YYDPRINTF ((stderr, "Now at end of input.\n"));
	} else {
		yytoken = YYTRANSLATE (yychar);
		YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
	}

	/* If the proper action on seeing token YYTOKEN is to reduce or to
	   detect an error, take that action.  */
	yyn += yytoken;
	if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
		goto yydefault;
	yyn = yytable[yyn];
	if (yyn <= 0) {
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
	switch (yyn) {
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
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 6:
		/* Line 1787 of yacc.c  */
#line 101 "promela.ypp"
		{
			(yyval.node) = ctx->value(PML_NAME, (yyvsp[(1) - (1)].value));
			free((yyvsp[(1) - (1)].value));
		}
		break;

	case 7:
		/* Line 1787 of yacc.c  */
#line 102 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_VAR_ARRAY, 2, ctx->value(PML_NAME, (yyvsp[(1) - (4)].value)), (yyvsp[(3) - (4)].node));
			free((yyvsp[(1) - (4)].value));
		}
		break;

	case 8:
		/* Line 1787 of yacc.c  */
#line 106 "promela.ypp"
		{
			if ((yyvsp[(2) - (2)].node) != NULL) {
				if ((yyvsp[(2) - (2)].node)->type == PML_CMPND) {
					(yyval.node) = ctx->node(PML_CMPND, 1, (yyvsp[(1) - (2)].node));
					(yyval.node)->merge((yyvsp[(2) - (2)].node));
					delete (yyvsp[(2) - (2)].node);
				} else {
					(yyval.node) = ctx->node(PML_CMPND, 2, (yyvsp[(1) - (2)].node), (yyvsp[(2) - (2)].node));
				}
			} else {
				/*						$$ = ctx->node(PML_CMPND, 1, $1);*/
				(yyval.node) = (yyvsp[(1) - (2)].node);
			}
			/*					if ($2 != NULL) {
									$$ = ctx->node(PML_CMPND, 1, $1);
									if ($2->operands.size() > 0) {
										$$->merge($2);
										delete $2;
									} else {
										$$->push($2);
									}
								} else {
									$$ = $1;
								}
			*/
		}
		break;

	case 9:
		/* Line 1787 of yacc.c  */
#line 132 "promela.ypp"
		{
			(yyval.node) = NULL;
		}
		break;

	case 10:
		/* Line 1787 of yacc.c  */
#line 133 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(2) - (2)].node);
		}
		break;

	case 11:
		/* Line 1787 of yacc.c  */
#line 143 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(2) - (3)].node);
		}
		break;

	case 12:
		/* Line 1787 of yacc.c  */
#line 144 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_PLUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 13:
		/* Line 1787 of yacc.c  */
#line 145 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_MINUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 14:
		/* Line 1787 of yacc.c  */
#line 146 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_TIMES, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 15:
		/* Line 1787 of yacc.c  */
#line 147 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_DIVIDE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 16:
		/* Line 1787 of yacc.c  */
#line 148 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_MODULO, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 17:
		/* Line 1787 of yacc.c  */
#line 149 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_BITAND, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 18:
		/* Line 1787 of yacc.c  */
#line 150 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_BITXOR, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 19:
		/* Line 1787 of yacc.c  */
#line 151 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_BITOR, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 20:
		/* Line 1787 of yacc.c  */
#line 152 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_GT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 21:
		/* Line 1787 of yacc.c  */
#line 153 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_LT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 22:
		/* Line 1787 of yacc.c  */
#line 154 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_GE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 23:
		/* Line 1787 of yacc.c  */
#line 155 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_LE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 24:
		/* Line 1787 of yacc.c  */
#line 156 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_EQ, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 25:
		/* Line 1787 of yacc.c  */
#line 157 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_NE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 26:
		/* Line 1787 of yacc.c  */
#line 158 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_AND, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 27:
		/* Line 1787 of yacc.c  */
#line 159 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_OR, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 28:
		/* Line 1787 of yacc.c  */
#line 160 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_LSHIFT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 29:
		/* Line 1787 of yacc.c  */
#line 161 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_RSHIFT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 30:
		/* Line 1787 of yacc.c  */
#line 162 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_NEG, 1, (yyvsp[(2) - (2)].node));
		}
		break;

	case 31:
		/* Line 1787 of yacc.c  */
#line 163 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_MINUS, 1, (yyvsp[(2) - (2)].node));
		}
		break;

	case 32:
		/* Line 1787 of yacc.c  */
#line 165 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_LEN, 1, (yyvsp[(3) - (4)].node));
		}
		break;

	case 33:
		/* Line 1787 of yacc.c  */
#line 166 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 34:
		/* Line 1787 of yacc.c  */
#line 167 "promela.ypp"
		{
			(yyval.node) = ctx->value(PML_CONST, (yyvsp[(1) - (1)].value));
			free((yyvsp[(1) - (1)].value));
		}
		break;

	case 35:
		/* Line 1787 of yacc.c  */
#line 168 "promela.ypp"
		{
			/* Non standard promela for string literals */
			(yyval.node) = ctx->value(PML_STRING, (yyvsp[(1) - (1)].value));
			free((yyvsp[(1) - (1)].value));
		}
		break;

	case 36:
		/* Line 1787 of yacc.c  */
#line 174 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_SHOW, 0);
		}
		break;

	case 37:
		/* Line 1787 of yacc.c  */
#line 175 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_HIDDEN, 0);
		}
		break;

	case 38:
		/* Line 1787 of yacc.c  */
#line 176 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_SHOW, 0);
		}
		break;

	case 39:
		/* Line 1787 of yacc.c  */
#line 177 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_ISLOCAL, 0);
		}
		break;

	case 40:
		/* Line 1787 of yacc.c  */
#line 180 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_DECL, 3, (yyvsp[(1) - (3)].node), ctx->value(PML_TYPE, (yyvsp[(2) - (3)].value)), (yyvsp[(3) - (3)].node));
			free((yyvsp[(2) - (3)].value));
		}
		break;

	case 41:
		/* Line 1787 of yacc.c  */
#line 181 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_UNAME, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 42:
		/* Line 1787 of yacc.c  */
#line 182 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_DECL, 3, (yyvsp[(1) - (6)].node), ctx->value(PML_TYPE, (yyvsp[(2) - (6)].value)), (yyvsp[(5) - (6)].node));
			free((yyvsp[(2) - (6)].value));
		}
		break;

	case 43:
		/* Line 1787 of yacc.c  */
#line 183 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(2) - (2)].node);
		}
		break;

	case 44:
		/* Line 1787 of yacc.c  */
#line 186 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_TYPEDEF, 2, ctx->value(PML_NAME, (yyvsp[(2) - (5)].value)), (yyvsp[(4) - (5)].node));
		}
		break;

	case 45:
		/* Line 1787 of yacc.c  */
#line 189 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 46:
		/* Line 1787 of yacc.c  */
#line 190 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (2)].node);
		}
		break;

	case 47:
		/* Line 1787 of yacc.c  */
#line 191 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_DECLLIST, 1, (yyvsp[(1) - (3)].node));
			if((yyvsp[(3) - (3)].node)->type == PML_DECLLIST) {
				(yyval.node)->merge((yyvsp[(3) - (3)].node));
				delete (yyvsp[(3) - (3)].node);
			} else {
				(yyval.node)->push((yyvsp[(3) - (3)].node));
			}
		}
		break;

	case 48:
		/* Line 1787 of yacc.c  */
#line 201 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_VARLIST, 1, (yyvsp[(1) - (1)].node));
		}
		break;

	case 49:
		/* Line 1787 of yacc.c  */
#line 202 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_VARLIST, 1, (yyvsp[(1) - (3)].node));
			(yyval.node)->merge((yyvsp[(3) - (3)].node));
			delete (yyvsp[(3) - (3)].node);
		}
		break;

	case 50:
		/* Line 1787 of yacc.c  */
#line 205 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 51:
		/* Line 1787 of yacc.c  */
#line 206 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_ASGN, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 52:
		/* Line 1787 of yacc.c  */
#line 209 "promela.ypp"
		{
			(yyval.node) = ctx->value(PML_NAME, (yyvsp[(1) - (1)].value));
			free((yyvsp[(1) - (1)].value));
		}
		break;

	case 53:
		/* Line 1787 of yacc.c  */
#line 210 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_COLON, 2, ctx->value(PML_NAME, (yyvsp[(1) - (3)].value)), ctx->value(PML_CONST, (yyvsp[(3) - (3)].value)));
			free((yyvsp[(1) - (3)].value));
			free((yyvsp[(3) - (3)].value));
		}
		break;

	case 54:
		/* Line 1787 of yacc.c  */
#line 211 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_VAR_ARRAY, 2, ctx->value(PML_NAME, (yyvsp[(1) - (4)].value)), (yyvsp[(3) - (4)].node));
			free((yyvsp[(1) - (4)].value));
		}
		break;

	case 55:
		/* Line 1787 of yacc.c  */
#line 214 "promela.ypp"
		{
			(yyval.node) = ctx->value(PML_CONST, (yyvsp[(1) - (1)].value));
			free((yyvsp[(1) - (1)].value));
		}
		break;

	case 56:
		/* Line 1787 of yacc.c  */
#line 215 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_MINUS, 1, (yyvsp[(2) - (2)].node));
		}
		break;

	case 57:
		/* Line 1787 of yacc.c  */
#line 216 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(2) - (3)].node);
		}
		break;

	case 58:
		/* Line 1787 of yacc.c  */
#line 217 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_PLUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 59:
		/* Line 1787 of yacc.c  */
#line 218 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_MINUS, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 60:
		/* Line 1787 of yacc.c  */
#line 219 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_TIMES, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 61:
		/* Line 1787 of yacc.c  */
#line 220 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_DIVIDE, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 62:
		/* Line 1787 of yacc.c  */
#line 221 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_MODULO, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 63:
		/* Line 1787 of yacc.c  */
#line 224 "promela.ypp"
		{
			(yyval.node) = ctx->value(PML_NAME, (yyvsp[(1) - (1)].value));
			free((yyvsp[(1) - (1)].value));
		}
		break;

	case 64:
		/* Line 1787 of yacc.c  */
#line 225 "promela.ypp"
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

	case 65:
		/* Line 1787 of yacc.c  */
#line 234 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (2)].node);
		}
		break;

	case 66:
		/* Line 1787 of yacc.c  */
#line 237 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 67:
		/* Line 1787 of yacc.c  */
#line 238 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (2)].node);
		}
		break;

	case 68:
		/* Line 1787 of yacc.c  */
#line 239 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_STMNT, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 69:
		/* Line 1787 of yacc.c  */
#line 242 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 70:
		/* Line 1787 of yacc.c  */
#line 245 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_ASGN, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;

	case 71:
		/* Line 1787 of yacc.c  */
#line 246 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_INCR, 1, (yyvsp[(1) - (2)].node));
		}
		break;

	case 72:
		/* Line 1787 of yacc.c  */
#line 247 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_DECR, 1, (yyvsp[(1) - (2)].node));
		}
		break;

	case 73:
		/* Line 1787 of yacc.c  */
#line 248 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_PRINT, 2, ctx->value(PML_STRING, (yyvsp[(3) - (5)].value)), (yyvsp[(4) - (5)].node));
			free((yyvsp[(3) - (5)].value));
		}
		break;

	case 74:
		/* Line 1787 of yacc.c  */
#line 249 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_PRINTM, 1, (yyvsp[(3) - (4)].node));
		}
		break;

	case 75:
		/* Line 1787 of yacc.c  */
#line 250 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_PRINTM, 1, ctx->value(PML_CONST, (yyvsp[(3) - (4)].value)));
			free((yyvsp[(3) - (4)].value));
		}
		break;

	case 76:
		/* Line 1787 of yacc.c  */
#line 251 "promela.ypp"
		{
			(yyval.node) = ctx->node(PML_ASSERT, 1, (yyvsp[(2) - (2)].node));
		}
		break;

	case 77:
		/* Line 1787 of yacc.c  */
#line 252 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 78:
		/* Line 1787 of yacc.c  */
#line 253 "promela.ypp"
		{  }
		break;

	case 79:
		/* Line 1787 of yacc.c  */
#line 253 "promela.ypp"
		{  }
		break;

	case 80:
		/* Line 1787 of yacc.c  */
#line 256 "promela.ypp"
		{  }
		break;

	case 81:
		/* Line 1787 of yacc.c  */
#line 257 "promela.ypp"
		{  }
		break;

	case 82:
		/* Line 1787 of yacc.c  */
#line 260 "promela.ypp"
		{
			(yyval.node) = ctx->value(0, "");
		}
		break;

	case 83:
		/* Line 1787 of yacc.c  */
#line 261 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(2) - (2)].node);
		}
		break;

	case 84:
		/* Line 1787 of yacc.c  */
#line 264 "promela.ypp"
		{
			(yyval.node) = (yyvsp[(1) - (1)].node);
		}
		break;

	case 85:
		/* Line 1787 of yacc.c  */
#line 265 "promela.ypp"
		{
			(yyval.node) = ctx->node(0, 2, (yyvsp[(1) - (3)].node), (yyvsp[(3) - (3)].node));
		}
		break;


		/* Line 1787 of yacc.c  */
#line 2207 "promela.tab.cpp"
	default:
		break;
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
	if (!yyerrstatus) {
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
			else if (yysyntax_error_status == 1) {
				if (yymsg != yymsgbuf)
					YYSTACK_FREE (yymsg);
				yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
				if (!yymsg) {
					yymsg = yymsgbuf;
					yymsg_alloc = sizeof yymsgbuf;
					yysyntax_error_status = 2;
				} else {
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



	if (yyerrstatus == 3) {
		/* If just tried and failed to reuse lookahead token after an
		error, discard it.  */

		if (yychar <= YYEOF) {
			/* Return failure if at end of input.  */
			if (yychar == YYEOF)
				YYABORT;
		} else {
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

	for (;;) {
		yyn = yypact[yystate];
		if (!yypact_value_is_default (yyn)) {
			yyn += YYTERROR;
			if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR) {
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
	if (yychar != YYEMPTY) {
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
	while (yyssp != yyss) {
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
#line 269 "promela.ypp"


