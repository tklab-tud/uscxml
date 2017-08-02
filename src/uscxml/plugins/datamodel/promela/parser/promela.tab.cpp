/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

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
#define YYBISON_VERSION "3.0.4"

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
#define YYLTYPE         PROMELA_LTYPE
/* Substitute the variable and function names.  */
#define yyparse         promela_parse
#define yylex           promela_lex
#define yyerror         promela_error
#define yydebug         promela_debug
#define yynerrs         promela_nerrs


/* Copy the first part of user declarations.  */
#line 14 "promela.ypp" /* yacc.c:339  */

#include "../PromelaParser.h"
#include "promela.tab.hpp"
#include <sys/types.h>
#include <stdarg.h>

#define YYMAXDEPTH	20000	// default is 10000
#define YYDEBUG		1
#define YYERROR_VERBOSE 1

extern int promela_lex (PROMELA_STYPE* yylval_param, PROMELA_LTYPE* yylloc_param, void* yyscanner);

using namespace uscxml;

#line 89 "promela.tab.cpp" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
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
/* Debug traces.  */
#ifndef PROMELA_DEBUG
# if defined YYDEBUG
#if YYDEBUG
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

/* Token type.  */
#ifndef PROMELA_TOKENTYPE
# define PROMELA_TOKENTYPE
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
	PML_UNREC = 306,
	PML_ASGN = 307,
	PML_OR = 308,
	PML_AND = 309,
	PML_BITOR = 310,
	PML_BITXOR = 311,
	PML_BITAND = 312,
	PML_EQ = 313,
	PML_NE = 314,
	PML_GT = 315,
	PML_LT = 316,
	PML_GE = 317,
	PML_LE = 318,
	PML_LSHIFT = 319,
	PML_RSHIFT = 320,
	PML_PLUS = 321,
	PML_MINUS = 322,
	PML_TIMES = 323,
	PML_DIVIDE = 324,
	PML_MODULO = 325,
	PML_INCR = 326,
	PML_DECR = 327,
	PML_COMPL = 328,
	PML_NEG = 329,
	PML_DOT = 330,
	PML_CMPND = 331
};
#endif

/* Value type.  */
#if ! defined PROMELA_STYPE && ! defined PROMELA_STYPE_IS_DECLARED

union PROMELA_STYPE {
#line 39 "promela.ypp" /* yacc.c:355  */

	uscxml::PromelaParserNode* node;
	char* value;

#line 219 "promela.tab.cpp" /* yacc.c:355  */
};

typedef union PROMELA_STYPE PROMELA_STYPE;
# define PROMELA_STYPE_IS_TRIVIAL 1
# define PROMELA_STYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined PROMELA_LTYPE && ! defined PROMELA_LTYPE_IS_DECLARED
typedef struct PROMELA_LTYPE PROMELA_LTYPE;
struct PROMELA_LTYPE {
	int first_line;
	int first_column;
	int last_line;
	int last_column;
};
# define PROMELA_LTYPE_IS_DECLARED 1
# define PROMELA_LTYPE_IS_TRIVIAL 1
#endif



int promela_parse (uscxml::PromelaParser* ctx, void * scanner);

#endif /* !YY_PROMELA_PROMELA_TAB_HPP_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 249 "promela.tab.cpp" /* yacc.c:358  */

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
#else
typedef signed char yytype_int8;
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
# elif ! defined YYSIZE_T
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

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
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
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
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
/* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
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
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined PROMELA_LTYPE_IS_TRIVIAL && PROMELA_LTYPE_IS_TRIVIAL \
             && defined PROMELA_STYPE_IS_TRIVIAL && PROMELA_STYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc {
	yytype_int16 yyss_alloc;
	YYSTYPE yyvs_alloc;
	YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

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
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  32
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   288

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  83
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  21
/* YYNRULES -- Number of rules.  */
#define YYNRULES  81
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  143

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   331

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
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
	81,    82
};

#if PROMELA_DEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] = {
	0,    85,    85,    89,    93,    99,   102,   103,   106,   121,
	122,   132,   133,   134,   135,   136,   137,   138,   139,   140,
	141,   142,   143,   144,   145,   146,   147,   148,   149,   150,
	151,   152,   154,   155,   156,   157,   163,   164,   165,   166,
	169,   170,   171,   172,   175,   178,   179,   180,   190,   191,
	194,   195,   198,   199,   200,   203,   204,   205,   206,   207,
	208,   209,   210,   213,   214,   223,   226,   227,   228,   231,
	234,   235,   236,   237,   238,   239,   240,   241,   244,   245,
	248,   249
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
	"PML_COMMA", "PML_UNREC", "PML_ASGN", "PML_OR", "PML_AND", "PML_BITOR",
	"PML_BITXOR", "PML_BITAND", "PML_EQ", "PML_NE", "PML_GT", "PML_LT",
	"PML_GE", "PML_LE", "PML_LSHIFT", "PML_RSHIFT", "PML_PLUS", "PML_MINUS",
	"PML_TIMES", "PML_DIVIDE", "PML_MODULO", "PML_INCR", "PML_DECR",
	"PML_COMPL", "PML_NEG", "PML_DOT", "PML_CMPND", "$accept", "program",
	"varref", "pfld", "cmpnd", "sfld", "expr", "vis", "one_decl", "utype",
	"decl_lst", "var_list", "ivar", "vardcl", "const_expr", "nlst",
	"stmnt_lst", "stmnt", "Stmnt", "prargs", "arg", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] = {
	0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
	265,    40,    41,    91,    93,   123,   125,   266,   267,   268,
	269,   270,   271,   272,   273,   274,   275,   276,   277,   278,
	279,   280,   281,   282,   283,   284,   285,   286,   287,   288,
	289,   290,   291,   292,   293,   294,   295,   296,   297,   298,
	299,   300,   301,   302,   303,   304,   305,   306,   307,   308,
	309,   310,   311,   312,   313,   314,   315,   316,   317,   318,
	319,   320,   321,   322,   323,   324,   325,   326,   327,   328,
	329,   330,   331
};
# endif

#define YYPACT_NINF -112

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-112)))

#define YYTABLE_NINF -78

#define yytable_value_is_error(Yytable_value) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] = {
	14,    54,    54,    -6,    -3,  -112,  -112,  -112,  -112,  -112,
	2,    54,    54,    24,   -51,   -53,  -112,   140,    64,     5,
	-112,  -112,     6,  -112,  -112,    76,   182,    69,    41,    54,
	30,  -112,  -112,    54,  -112,  -112,    41,  -112,    54,    54,
	54,    54,    54,    54,    54,    54,    54,    54,    54,    54,
	54,    54,    54,    54,    54,    54,    43,   -45,    45,  -112,
	175,    52,  -112,    11,    86,    89,    95,    94,   182,  -112,
	198,   198,   112,   112,   112,   209,   209,    48,    48,    48,
	48,   120,   120,    30,    30,  -112,  -112,  -112,    97,     1,
	100,  -112,    60,    70,  -112,  -112,   182,  -112,    54,   114,
	-112,  -112,  -112,  -112,   130,    85,    19,    83,    45,    54,
	164,  -112,  -112,   117,  -112,    19,  -112,    19,     9,  -112,
	55,  -112,   182,    54,  -112,     4,   212,  -112,    19,    19,
	19,    19,    19,  -112,  -112,  -112,  -112,  -112,   212,   212,
	-112,  -112,  -112
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] = {
	36,     0,     0,     0,     0,    35,    37,    38,    39,    34,
	6,     0,     0,     0,    33,     9,     5,     4,     0,    45,
	2,     3,    66,    69,    33,     0,    76,     0,     0,     0,
	31,    30,     1,     0,    71,    72,     0,     8,     0,     0,
	0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
	0,     0,     0,     0,     0,     0,     0,     0,     0,    43,
	36,    67,    11,    78,     0,     0,     0,     0,    70,    10,
	27,    26,    19,    18,    17,    24,    25,    20,    21,    22,
	23,    28,    29,    12,    13,    14,    15,    16,     0,    52,
	0,    40,    48,    50,    41,    47,    77,    68,     0,     0,
	75,    74,    32,     7,    36,     0,     0,     0,     0,     0,
	80,    79,    73,     0,    53,     0,    55,     0,     0,    63,
	0,    49,    51,     0,    44,     0,    56,    54,     0,     0,
	0,     0,     0,    42,    64,    65,    81,    57,    58,    59,
	60,    61,    62
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] = {
	-112,  -112,    68,  -112,   153,  -112,     0,  -112,  -112,  -112,
	-38,   -48,  -112,  -112,  -111,  -112,   129,  -112,  -112,  -112,
	74
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] = {
	-1,    13,    24,    15,    16,    37,   110,    18,    19,    59,
	20,    91,    92,    93,   118,   120,    21,    22,    23,    99,
	111
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] = {
	17,    25,    26,    89,   125,    27,   126,    33,    28,   105,
	94,    30,    31,    90,   106,    29,   137,   138,   139,   140,
	141,   142,    95,   127,    32,     1,    34,    35,    36,    67,
	115,     2,     3,    68,     4,     5,    60,    61,    70,    71,
	72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
	82,    83,    84,    85,    86,    87,     6,     7,     8,     9,
	121,    96,    10,     1,   116,     1,   113,    98,    14,     2,
	3,   133,     4,     5,     4,     5,   128,   129,   130,   131,
	132,   128,   129,   130,   131,   132,    56,    11,    62,    10,
	63,    88,   117,    89,    12,    65,    66,     9,   100,     9,
	10,   101,    10,   134,    53,    54,    55,   102,   103,   122,
	57,   135,   104,    58,    64,   107,   108,    10,    49,    50,
	51,    52,    53,    54,    55,    11,   112,    11,   109,    14,
	114,   119,    12,   124,    12,    38,    39,    40,    41,    42,
	43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
	53,    54,    55,    38,    39,    40,    41,    42,    43,    44,
	45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
	55,   -77,     6,     7,     8,   -46,    43,    44,    45,    46,
	47,    48,    49,    50,    51,    52,    53,    54,    55,    69,
	97,   -46,    51,    52,    53,    54,    55,   136,     0,    38,
	39,    40,    41,    42,    43,    44,    45,    46,    47,    48,
	49,    50,    51,    52,    53,    54,    55,     6,     7,     8,
	123,     0,     0,    38,    39,    40,    41,    42,    43,    44,
	45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
	55,    38,    39,    40,    41,    42,    43,    44,    45,    46,
	47,    48,    49,    50,    51,    52,    53,    54,    55,    40,
	41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
	51,    52,    53,    54,    55,    45,    46,    47,    48,    49,
	50,    51,    52,    53,    54,    55,   130,   131,   132
};

static const yytype_int16 yycheck[] = {
	0,     1,     2,    48,   115,    11,   117,    58,    11,     8,
	58,    11,    12,    58,    13,    13,    12,   128,   129,   130,
	131,   132,    60,    14,     0,    11,    77,    78,    81,    29,
	11,    17,    18,    33,    20,    21,    31,    31,    38,    39,
	40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
	50,    51,    52,    53,    54,    55,    42,    43,    44,    45,
	108,    61,    48,    11,    45,    11,   104,    56,     0,    17,
	18,    16,    20,    21,    20,    21,    72,    73,    74,    75,
	76,    72,    73,    74,    75,    76,    22,    73,    12,    48,
	21,    48,    73,    48,    80,    27,    28,    45,    12,    45,
	48,    12,    48,    48,    74,    75,    76,    12,    14,   109,
	46,    56,    15,    49,    45,    15,    56,    48,    70,    71,
	72,    73,    74,    75,    76,    73,    12,    73,    58,    61,
	45,    48,    80,    16,    80,    59,    60,    61,    62,    63,
	64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
	74,    75,    76,    59,    60,    61,    62,    63,    64,    65,
	66,    67,    68,    69,    70,    71,    72,    73,    74,    75,
	76,    31,    42,    43,    44,     0,    64,    65,    66,    67,
	68,    69,    70,    71,    72,    73,    74,    75,    76,    36,
	61,    16,    72,    73,    74,    75,    76,   123,    -1,    59,
	60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
	70,    71,    72,    73,    74,    75,    76,    42,    43,    44,
	56,    -1,    -1,    59,    60,    61,    62,    63,    64,    65,
	66,    67,    68,    69,    70,    71,    72,    73,    74,    75,
	76,    59,    60,    61,    62,    63,    64,    65,    66,    67,
	68,    69,    70,    71,    72,    73,    74,    75,    76,    61,
	62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
	72,    73,    74,    75,    76,    66,    67,    68,    69,    70,
	71,    72,    73,    74,    75,    76,    74,    75,    76
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] = {
	0,    11,    17,    18,    20,    21,    42,    43,    44,    45,
	48,    73,    80,    84,    85,    86,    87,    89,    90,    91,
	93,    99,   100,   101,    85,    89,    89,    11,    11,    13,
	89,    89,     0,    58,    77,    78,    81,    88,    59,    60,
	61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
	71,    72,    73,    74,    75,    76,    22,    46,    49,    92,
	31,    31,    12,    21,    45,    85,    85,    89,    89,    87,
	89,    89,    89,    89,    89,    89,    89,    89,    89,    89,
	89,    89,    89,    89,    89,    89,    89,    89,    48,    48,
	58,    94,    95,    96,    94,    93,    89,    99,    56,   102,
	12,    12,    12,    14,    15,     8,    13,    15,    56,    58,
	89,   103,    12,    93,    45,    11,    45,    73,    97,    48,
	98,    94,    89,    56,    16,    97,    97,    14,    72,    73,
	74,    75,    76,    16,    48,    56,   103,    12,    97,    97,
	97,    97,    97
};

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] = {
	0,    83,    84,    84,    84,    85,    86,    86,    87,    88,
	88,    89,    89,    89,    89,    89,    89,    89,    89,    89,
	89,    89,    89,    89,    89,    89,    89,    89,    89,    89,
	89,    89,    89,    89,    89,    89,    90,    90,    90,    90,
	91,    91,    91,    91,    92,    93,    93,    93,    94,    94,
	95,    95,    96,    96,    96,    97,    97,    97,    97,    97,
	97,    97,    97,    98,    98,    98,    99,    99,    99,   100,
	101,   101,   101,   101,   101,   101,   101,   101,   102,   102,
	103,   103
};

/* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] = {
	0,     2,     1,     1,     1,     1,     1,     4,     2,     0,
	2,     3,     3,     3,     3,     3,     3,     3,     3,     3,
	3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
	2,     2,     4,     1,     1,     1,     0,     1,     1,     1,
	3,     3,     6,     2,     5,     1,     2,     3,     1,     3,
	1,     3,     1,     3,     4,     1,     2,     3,     3,     3,
	3,     3,     3,     1,     2,     2,     1,     2,     3,     1,
	3,     2,     2,     5,     4,     4,     2,     1,     0,     2,
	1,     3
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


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
      yyerror (&yylloc, ctx, scanner, YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if PROMELA_DEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined PROMELA_LTYPE_IS_TRIVIAL && PROMELA_LTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp) {
	unsigned res = 0;
	int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
	if (0 <= yylocp->first_line) {
		res += YYFPRINTF (yyo, "%d", yylocp->first_line);
		if (0 <= yylocp->first_column)
			res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
	}
	if (0 <= yylocp->last_line) {
		if (yylocp->first_line < yylocp->last_line) {
			res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
			if (0 <= end_col)
				res += YYFPRINTF (yyo, ".%d", end_col);
		} else if (0 <= end_col && yylocp->first_column < end_col)
			res += YYFPRINTF (yyo, "-%d", end_col);
	}
	return res;
}

#  define YY_LOCATION_PRINT(File, Loc)          \
  yy_location_print_ (File, &(Loc))

# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, Location, ctx, scanner); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, uscxml::PromelaParser* ctx, void * scanner) {
	FILE *yyo = yyoutput;
	YYUSE (yyo);
	YYUSE (yylocationp);
	YYUSE (ctx);
	YYUSE (scanner);
	if (!yyvaluep)
		return;
# ifdef YYPRINT
	if (yytype < YYNTOKENS)
		YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
	YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, uscxml::PromelaParser* ctx, void * scanner) {
	YYFPRINTF (yyoutput, "%s %s (",
	           yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

	YY_LOCATION_PRINT (yyoutput, *yylocationp);
	YYFPRINTF (yyoutput, ": ");
	yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, ctx, scanner);
	YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop) {
	YYFPRINTF (stderr, "Stack now");
	for (; yybottom <= yytop; yybottom++) {
		int yybot = *yybottom;
		YYFPRINTF (stderr, " %d", yybot);
	}
	YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, uscxml::PromelaParser* ctx, void * scanner) {
	unsigned long int yylno = yyrline[yyrule];
	int yynrhs = yyr2[yyrule];
	int yyi;
	YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	           yyrule - 1, yylno);
	/* The symbols being reduced.  */
	for (yyi = 0; yyi < yynrhs; yyi++) {
		YYFPRINTF (stderr, "   $%d = ", yyi + 1);
		yy_symbol_print (stderr,
		                 yystos[yyssp[yyi + 1 - yynrhs]],
		                 &(yyvsp[(yyi + 1) - (yynrhs)])
		                 , &(yylsp[(yyi + 1) - (yynrhs)])                       , ctx, scanner);
		YYFPRINTF (stderr, "\n");
	}
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, ctx, scanner); \
} while (0)

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
#ifndef YYINITDEPTH
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
static YYSIZE_T
yystrlen (const char *yystr) {
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
static char *
yystpcpy (char *yydest, const char *yysrc) {
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
	YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
	YYSIZE_T yysize = yysize0;
	enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
	/* Internationalized format string. */
	const char *yyformat = YY_NULLPTR;
	/* Arguments of yyformat. */
	char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
	/* Number of reported tokens (one for the "unexpected", one per
	   "expected"). */
	int yycount = 0;

	/* There are many possibilities here to consider:
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
						YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
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

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, uscxml::PromelaParser* ctx, void * scanner) {
	YYUSE (yyvaluep);
	YYUSE (yylocationp);
	YYUSE (ctx);
	YYUSE (scanner);
	if (!yymsg)
		yymsg = "Deleting";
	YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

	YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
	YYUSE (yytype);
	YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/*----------.
| yyparse.  |
`----------*/

int
yyparse (uscxml::PromelaParser* ctx, void * scanner) {
	/* The lookahead symbol.  */
	int yychar;


	/* The semantic value of the lookahead symbol.  */
	/* Default value used for initialization, for pacifying older GCCs
	   or non-GCC compilers.  */
	YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
	YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

	/* Location data for the lookahead symbol.  */
	static YYLTYPE yyloc_default
# if defined PROMELA_LTYPE_IS_TRIVIAL && PROMELA_LTYPE_IS_TRIVIAL
	    = { 1, 1, 1, 1 }
# endif
	      ;
	YYLTYPE yylloc = yyloc_default;

	/* Number of syntax errors so far.  */
	int yynerrs;

	int yystate;
	/* Number of tokens to shift before error messages enabled.  */
	int yyerrstatus;

	/* The stacks and their tools:
	   'yyss': related to states.
	   'yyvs': related to semantic values.
	   'yyls': related to locations.

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

	/* The location stack.  */
	YYLTYPE yylsa[YYINITDEPTH];
	YYLTYPE *yyls;
	YYLTYPE *yylsp;

	/* The locations where the error started and ended.  */
	YYLTYPE yyerror_range[3];

	YYSIZE_T yystacksize;

	int yyn;
	int yyresult;
	/* Lookahead token as an internal (translated) token number.  */
	int yytoken = 0;
	/* The variables used to return semantic value and location from the
	   action routines.  */
	YYSTYPE yyval;
	YYLTYPE yyloc;

#if YYERROR_VERBOSE
	/* Buffer for error messages, and its allocated size.  */
	char yymsgbuf[128];
	char *yymsg = yymsgbuf;
	YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

	/* The number of symbols on the RHS of the reduced rule.
	   Keep to zero when no symbol should be popped.  */
	int yylen = 0;

	yyssp = yyss = yyssa;
	yyvsp = yyvs = yyvsa;
	yylsp = yyls = yylsa;
	yystacksize = YYINITDEPTH;

	YYDPRINTF ((stderr, "Starting parse\n"));

	yystate = 0;
	yyerrstatus = 0;
	yynerrs = 0;
	yychar = YYEMPTY; /* Cause a token to be read.  */
	yylsp[0] = yylloc;
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
			YYLTYPE *yyls1 = yyls;

			/* Each stack pointer address is followed by the size of the
			   data in use in that stack, in bytes.  This used to be a
			   conditional around just the two extra args, but that might
			   be undefined if yyoverflow is a macro.  */
			yyoverflow (YY_("memory exhausted"),
			            &yyss1, yysize * sizeof (*yyssp),
			            &yyvs1, yysize * sizeof (*yyvsp),
			            &yyls1, yysize * sizeof (*yylsp),
			            &yystacksize);

			yyls = yyls1;
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
			YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
			if (yyss1 != yyssa)
				YYSTACK_FREE (yyss1);
		}
# endif
#endif /* no yyoverflow */

		yyssp = yyss + yysize - 1;
		yyvsp = yyvs + yysize - 1;
		yylsp = yyls + yysize - 1;

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
		yychar = yylex (&yylval, &yylloc, scanner);
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
	*++yylsp = yylloc;
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
	   '$$ = $1'.

	   Otherwise, the following line sets YYVAL to garbage.
	   This behavior is undocumented and Bison
	   users should not rely upon it.  Assigning to YYVAL
	   unconditionally makes the parser a bit smaller, and it avoids a
	   GCC warning that YYVAL may be used uninitialized.  */
	yyval = yyvsp[1-yylen];

	/* Default location.  */
	YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
	YY_REDUCE_PRINT (yyn);
	switch (yyn) {
	case 2:
#line 85 "promela.ypp" /* yacc.c:1646  */
		{
			ctx->ast = (yyvsp[0].node);
			ctx->type = PromelaParser::PROMELA_DECL;
		}
#line 1580 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 3:
#line 89 "promela.ypp" /* yacc.c:1646  */
		{
			ctx->ast = (yyvsp[0].node);
			ctx->type = PromelaParser::PROMELA_STMNT;
		}
#line 1589 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 4:
#line 93 "promela.ypp" /* yacc.c:1646  */
		{
			ctx->ast = (yyvsp[0].node);
			ctx->type = PromelaParser::PROMELA_EXPR;
		}
#line 1598 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 5:
#line 99 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1604 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 6:
#line 102 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->value(PML_NAME, (void*)&((yylsp[0])), (yyvsp[0].value));
			free((yyvsp[0].value));
		}
#line 1610 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 7:
#line 103 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_VAR_ARRAY, 2, ctx->value(PML_NAME, (void*)&((yylsp[-3])), (yyvsp[-3].value)), (yyvsp[-1].node));
			free((yyvsp[-3].value));
		}
#line 1616 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 8:
#line 107 "promela.ypp" /* yacc.c:1646  */
		{
			if ((yyvsp[0].node) != NULL) {
				if ((yyvsp[0].node)->type == PML_CMPND) {
					(yyval.node) = ctx->node(PML_CMPND, 1, (yyvsp[-1].node));
					(yyval.node)->merge((yyvsp[0].node));
					delete (yyvsp[0].node);
				} else {
					(yyval.node) = ctx->node(PML_CMPND, 2, (yyvsp[-1].node), (yyvsp[0].node));
				}
			} else {
				(yyval.node) = (yyvsp[-1].node);
			}
		}
#line 1633 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 9:
#line 121 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = NULL;
		}
#line 1639 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 10:
#line 122 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1645 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 11:
#line 132 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[-1].node);
		}
#line 1651 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 12:
#line 133 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_PLUS, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1657 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 13:
#line 134 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_MINUS, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1663 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 14:
#line 135 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_TIMES, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1669 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 15:
#line 136 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_DIVIDE, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1675 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 16:
#line 137 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_MODULO, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1681 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 17:
#line 138 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_BITAND, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1687 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 18:
#line 139 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_BITXOR, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1693 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 19:
#line 140 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_BITOR, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1699 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 20:
#line 141 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_GT, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1705 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 21:
#line 142 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_LT, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1711 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 22:
#line 143 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_GE, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1717 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 23:
#line 144 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_LE, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1723 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 24:
#line 145 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_EQ, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1729 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 25:
#line 146 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_NE, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1735 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 26:
#line 147 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_AND, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1741 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 27:
#line 148 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_OR, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1747 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 28:
#line 149 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_LSHIFT, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1753 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 29:
#line 150 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_RSHIFT, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1759 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 30:
#line 151 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_NEG, 1, (yyvsp[0].node));
		}
#line 1765 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 31:
#line 152 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_MINUS, 1, (yyvsp[0].node));
		}
#line 1771 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 32:
#line 154 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_LEN, 1, (yyvsp[-1].node));
		}
#line 1777 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 33:
#line 155 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1783 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 34:
#line 156 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->value(PML_CONST, (void*)&((yylsp[0])), (yyvsp[0].value));
			free((yyvsp[0].value));
		}
#line 1789 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 35:
#line 157 "promela.ypp" /* yacc.c:1646  */
		{
			/* Non standard promela for string literals */
			(yyval.node) = ctx->value(PML_STRING, (void*)&((yylsp[0])), (yyvsp[0].value));
			free((yyvsp[0].value));
		}
#line 1797 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 36:
#line 163 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_SHOW, 0);
		}
#line 1803 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 37:
#line 164 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_HIDDEN, 0);
		}
#line 1809 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 38:
#line 165 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_SHOW, 0);
		}
#line 1815 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 39:
#line 166 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_ISLOCAL, 0);
		}
#line 1821 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 40:
#line 169 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_DECL, 3, (yyvsp[-2].node), ctx->value(PML_TYPE, (void*)&((yylsp[-1])), (yyvsp[-1].value)), (yyvsp[0].node));
			free((yyvsp[-1].value));
		}
#line 1827 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 41:
#line 170 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_UNAME, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1833 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 42:
#line 171 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_DECL, 3, (yyvsp[-5].node), ctx->value(PML_TYPE, (void*)&((yylsp[-4])), (yyvsp[-4].value)), (yyvsp[-1].node));
			free((yyvsp[-4].value));
		}
#line 1839 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 43:
#line 172 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1845 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 44:
#line 175 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_TYPEDEF, 2, ctx->value(PML_NAME, (void*)&((yylsp[-3])), (yyvsp[-3].value)), (yyvsp[-1].node));
		}
#line 1851 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 45:
#line 178 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1857 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 46:
#line 179 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[-1].node);
		}
#line 1863 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 47:
#line 180 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_DECLLIST, 1, (yyvsp[-2].node));
			if((yyvsp[0].node)->type == PML_DECLLIST) {
				(yyval.node)->merge((yyvsp[0].node));
				delete (yyvsp[0].node);
			} else {
				(yyval.node)->push((yyvsp[0].node));
			}
		}
#line 1876 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 48:
#line 190 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_VARLIST, 1, (yyvsp[0].node));
		}
#line 1882 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 49:
#line 191 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_VARLIST, 1, (yyvsp[-2].node));
			(yyval.node)->merge((yyvsp[0].node));
			delete (yyvsp[0].node);
		}
#line 1888 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 50:
#line 194 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1894 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 51:
#line 195 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_ASGN, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1900 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 52:
#line 198 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->value(PML_NAME, (void*)&((yylsp[0])), (yyvsp[0].value));
			free((yyvsp[0].value));
		}
#line 1906 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 53:
#line 199 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_COLON, 2, ctx->value(PML_NAME, (void*)&((yylsp[-2])), (yyvsp[-2].value)), ctx->value(PML_CONST, (void*)&((yylsp[0])), (yyvsp[0].value)));
			free((yyvsp[-2].value));
			free((yyvsp[0].value));
		}
#line 1912 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 54:
#line 200 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_VAR_ARRAY, 2, ctx->value(PML_NAME, (void*)&((yylsp[-3])), (yyvsp[-3].value)), (yyvsp[-1].node));
			free((yyvsp[-3].value));
		}
#line 1918 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 55:
#line 203 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->value(PML_CONST, (void*)&((yylsp[0])), (yyvsp[0].value));
			free((yyvsp[0].value));
		}
#line 1924 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 56:
#line 204 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_MINUS, 1, (yyvsp[0].node));
		}
#line 1930 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 57:
#line 205 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[-1].node);
		}
#line 1936 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 58:
#line 206 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_PLUS, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1942 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 59:
#line 207 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_MINUS, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1948 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 60:
#line 208 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_TIMES, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1954 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 61:
#line 209 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_DIVIDE, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1960 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 62:
#line 210 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_MODULO, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 1966 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 63:
#line 213 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->value(PML_NAME, (void*)&((yylsp[0])), (yyvsp[0].value));
			free((yyvsp[0].value));
		}
#line 1972 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 64:
#line 214 "promela.ypp" /* yacc.c:1646  */
		{
			if ((yyvsp[-1].node)->type == PML_NAME) {
				(yyval.node) = ctx->node(PML_NAMELIST, 1, (yyvsp[-1].node));
				(yyval.node)->push(ctx->value(PML_NAME, (void*)&((yylsp[0])), (yyvsp[0].value)));
			} else {
				(yyvsp[-1].node)->push(ctx->value(PML_NAME, (void*)&((yylsp[0])), (yyvsp[0].value)));
			}
			free((yyvsp[0].value));
		}
#line 1986 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 65:
#line 223 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[-1].node);
		}
#line 1992 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 66:
#line 226 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 1998 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 67:
#line 227 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[-1].node);
		}
#line 2004 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 68:
#line 228 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_STMNT, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 2010 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 69:
#line 231 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 2016 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 70:
#line 234 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_ASGN, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 2022 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 71:
#line 235 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_INCR, 1, (yyvsp[-1].node));
		}
#line 2028 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 72:
#line 236 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_DECR, 1, (yyvsp[-1].node));
		}
#line 2034 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 73:
#line 237 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_PRINT, 2, ctx->value(PML_STRING, (void*)&((yylsp[-2])), (yyvsp[-2].value)), (yyvsp[-1].node));
			free((yyvsp[-2].value));
		}
#line 2040 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 74:
#line 238 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_PRINT, 1, (yyvsp[-1].node));
		}
#line 2046 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 75:
#line 239 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_PRINT, 1, ctx->value(PML_CONST, (void*)&((yylsp[-1])), (yyvsp[-1].value)));
			free((yyvsp[-1].value));
		}
#line 2052 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 76:
#line 240 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(PML_ASSERT, 1, (yyvsp[0].node));
		}
#line 2058 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 77:
#line 241 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 2064 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 78:
#line 244 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->value(0, NULL, "");
		}
#line 2070 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 79:
#line 245 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 2076 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 80:
#line 248 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = (yyvsp[0].node);
		}
#line 2082 "promela.tab.cpp" /* yacc.c:1646  */
		break;

	case 81:
#line 249 "promela.ypp" /* yacc.c:1646  */
		{
			(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node));
		}
#line 2088 "promela.tab.cpp" /* yacc.c:1646  */
		break;


#line 2092 "promela.tab.cpp" /* yacc.c:1646  */
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
	*++yylsp = yyloc;

	/* Now 'shift' the result of the reduction.  Determine what state
	   that goes to, based on the state we popped back to and the rule
	   number reduced by.  */

	yyn = yyr1[yyn];

	yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
	if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
		yystate = yytable[yystate];
	else
		yystate = yydefgoto[yyn - YYNTOKENS];

	goto yynewstate;


	/*--------------------------------------.
	| yyerrlab -- here on detecting error.  |
	`--------------------------------------*/
yyerrlab:
	/* Make sure we have latest lookahead translation.  See comments at
	   user semantic actions for why this is necessary.  */
	yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

	/* If not already recovering from an error, report this error.  */
	if (!yyerrstatus) {
		++yynerrs;
#if ! YYERROR_VERBOSE
		yyerror (&yylloc, ctx, scanner, YY_("syntax error"));
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
			yyerror (&yylloc, ctx, scanner, yymsgp);
			if (yysyntax_error_status == 2)
				goto yyexhaustedlab;
		}
# undef YYSYNTAX_ERROR
#endif
	}

	yyerror_range[1] = yylloc;

	if (yyerrstatus == 3) {
		/* If just tried and failed to reuse lookahead token after an
		   error, discard it.  */

		if (yychar <= YYEOF) {
			/* Return failure if at end of input.  */
			if (yychar == YYEOF)
				YYABORT;
		} else {
			yydestruct ("Error: discarding",
			            yytoken, &yylval, &yylloc, ctx, scanner);
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

	yyerror_range[1] = yylsp[1-yylen];
	/* Do not reclaim the symbols of the rule whose action triggered
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
	yyerrstatus = 3;      /* Each real token shifted decrements this.  */

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

		yyerror_range[1] = *yylsp;
		yydestruct ("Error: popping",
		            yystos[yystate], yyvsp, yylsp, ctx, scanner);
		YYPOPSTACK (1);
		yystate = *yyssp;
		YY_STACK_PRINT (yyss, yyssp);
	}

	YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
	*++yyvsp = yylval;
	YY_IGNORE_MAYBE_UNINITIALIZED_END

	yyerror_range[2] = yylloc;
	/* Using YYLLOC is tempting, but would change the location of
	   the lookahead.  YYLOC is available though.  */
	YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
	*++yylsp = yyloc;

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
	yyerror (&yylloc, ctx, scanner, YY_("memory exhausted"));
	yyresult = 2;
	/* Fall through.  */
#endif

yyreturn:
	if (yychar != YYEMPTY) {
		/* Make sure we have latest lookahead translation.  See comments at
		   user semantic actions for why this is necessary.  */
		yytoken = YYTRANSLATE (yychar);
		yydestruct ("Cleanup: discarding lookahead",
		            yytoken, &yylval, &yylloc, ctx, scanner);
	}
	/* Do not reclaim the symbols of the rule whose action triggered
	   this YYABORT or YYACCEPT.  */
	YYPOPSTACK (yylen);
	YY_STACK_PRINT (yyss, yyssp);
	while (yyssp != yyss) {
		yydestruct ("Cleanup: popping",
		            yystos[*yyssp], yyvsp, yylsp, ctx, scanner);
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
	return yyresult;
}
#line 253 "promela.ypp" /* yacc.c:1906  */


