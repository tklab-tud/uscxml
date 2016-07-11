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
#define YYSTYPE         C89_STYPE
#define YYLTYPE         C89_LTYPE
/* Substitute the variable and function names.  */
#define yyparse         c89_parse
#define yylex           c89_lex
#define yyerror         c89_error
#define yydebug         c89_debug
#define yynerrs         c89_nerrs


/* Copy the first part of user declarations.  */
#line 1 "c89.ypp" /* yacc.c:339  */

#include "../C89Parser.h"
#include "c89.tab.hpp"
#include <sys/types.h>
#include <stdarg.h>

#define YYMAXDEPTH	20000	// default is 10000
#define YYDEBUG		1
#define YYERROR_VERBOSE 1

extern int c89_lex (C89_STYPE* yylval_param, C89_LTYPE* yylloc_param, void* yyscanner);

using namespace uscxml;

#line 89 "c89.tab.cpp" /* yacc.c:339  */

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
   by #include "c89.tab.hpp".  */
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
#line 26 "c89.ypp" /* yacc.c:355  */

  uscxml::C89ParserNode* node;
	char* value;

#line 203 "c89.tab.cpp" /* yacc.c:355  */
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

/* Copy the second part of user declarations.  */

#line 233 "c89.tab.cpp" /* yacc.c:358  */

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
         || (defined C89_LTYPE_IS_TRIVIAL && C89_LTYPE_IS_TRIVIAL \
             && defined C89_STYPE_IS_TRIVIAL && C89_STYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
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
#define YYFINAL  61
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   1301

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  85
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  64
/* YYNRULES -- Number of rules.  */
#define YYNRULES  212
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  350

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   315

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    72,     2,     2,     2,    74,    67,     2,
      61,    62,    68,    69,    66,    70,    65,    73,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    80,    82,
      75,    81,    76,    79,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    63,     2,    64,    77,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    83,    78,    84,    71,     2,     2,     2,
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
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60
};

#if C89_DEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    79,    79,    82,    85,    88,    94,    97,   100,   103,
     106,   109,   112,   115,   121,   124,   130,   133,   136,   139,
     142,   145,   151,   152,   153,   154,   155,   156,   160,   161,
     165,   166,   169,   172,   178,   179,   182,   188,   189,   192,
     198,   199,   202,   205,   208,   214,   215,   218,   224,   225,
     231,   232,   238,   239,   245,   246,   252,   253,   259,   260,
     266,   267,   273,   274,   275,   276,   277,   278,   279,   280,
     281,   282,   283,   287,   288,   294,   298,   299,   305,   306,
     309,   310,   313,   314,   320,   321,   327,   328,   334,   335,
     336,   337,   338,   342,   343,   344,   345,   346,   347,   348,
     349,   350,   351,   352,   353,   357,   360,   363,   369,   370,
     374,   375,   381,   387,   390,   391,   394,   398,   399,   405,
     406,   409,   415,   416,   417,   421,   422,   428,   431,   435,
     436,   440,   443,   447,   450,   453,   456,   459,   462,   465,
     471,   472,   473,   474,   478,   479,   486,   487,   491,   492,
     498,   501,   504,   508,   511,   517,   518,   524,   525,   526,
     530,   531,   532,   533,   534,   537,   538,   539,   540,   546,
     547,   550,   556,   557,   563,   564,   565,   566,   567,   568,
     572,   575,   578,   584,   587,   590,   593,   599,   600,   606,
     607,   613,   616,   622,   625,   628,   634,   637,   640,   643,
     649,   650,   651,   652,   653,   657,   658,   662,   663,   667,
     670,   673,   676
};
#endif

#if C89_DEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "IDENTIFIER", "CONSTANT",
  "STRING_LITERAL", "SIZEOF", "PTR_OP", "INC_OP", "DEC_OP", "LEFT_OP",
  "RIGHT_OP", "LE_OP", "GE_OP", "EQ_OP", "NE_OP", "AND_OP", "OR_OP",
  "MUL_ASSIGN", "DIV_ASSIGN", "MOD_ASSIGN", "ADD_ASSIGN", "SUB_ASSIGN",
  "LEFT_ASSIGN", "RIGHT_ASSIGN", "AND_ASSIGN", "XOR_ASSIGN", "OR_ASSIGN",
  "TYPE_NAME", "TYPEDEF", "EXTERN", "STATIC", "AUTO", "REGISTER", "CHAR",
  "SHORT", "INT", "LONG", "SIGNED", "UNSIGNED", "FLOAT", "DOUBLE", "CONST",
  "VOLATILE", "VOID", "STRUCT", "UNION", "ENUM", "ELLIPSIS", "CASE",
  "DEFAULT", "IF", "ELSE", "SWITCH", "WHILE", "DO", "FOR", "GOTO",
  "CONTINUE", "BREAK", "RETURN", "'('", "')'", "'['", "']'", "'.'", "','",
  "'&'", "'*'", "'+'", "'-'", "'~'", "'!'", "'/'", "'%'", "'<'", "'>'",
  "'^'", "'|'", "'?'", "':'", "'='", "';'", "'{'", "'}'", "$accept",
  "primary_expression", "postfix_expression", "argument_expression_list",
  "unary_expression", "unary_operator", "cast_expression",
  "multiplicative_expression", "additive_expression", "shift_expression",
  "relational_expression", "equality_expression", "and_expression",
  "exclusive_or_expression", "inclusive_or_expression",
  "logical_and_expression", "logical_or_expression",
  "conditional_expression", "assignment_expression", "assignment_operator",
  "expression", "constant_expression", "declaration",
  "declaration_specifiers", "init_declarator_list", "init_declarator",
  "storage_class_specifier", "type_specifier", "struct_or_union_specifier",
  "struct_or_union", "struct_declaration_list", "struct_declaration",
  "specifier_qualifier_list", "struct_declarator_list",
  "struct_declarator", "enum_specifier", "enumerator_list", "enumerator",
  "type_qualifier", "declarator", "direct_declarator", "pointer",
  "type_qualifier_list", "parameter_type_list", "parameter_list",
  "parameter_declaration", "identifier_list", "type_name",
  "abstract_declarator", "direct_abstract_declarator", "initializer",
  "initializer_list", "statement", "labeled_statement",
  "compound_statement", "declaration_list", "statement_list",
  "expression_statement", "selection_statement", "iteration_statement",
  "jump_statement", "translation_unit", "external_declaration",
  "function_definition", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,    40,    41,    91,    93,    46,    44,    38,    42,    43,
      45,   126,    33,    47,    37,    60,    62,    94,   124,    63,
      58,    61,    59,   123,   125
};
# endif

#define YYPACT_NINF -223

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-223)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     969,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
    -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,
    -223,     5,    42,     4,  -223,    31,  1254,  1254,  -223,    11,
    -223,  1254,  1101,    88,    26,   879,  -223,  -223,   -60,    51,
      14,  -223,  -223,     4,  -223,    38,  -223,  1081,  -223,  -223,
     -10,  1055,  -223,   278,  -223,    31,  -223,  1101,   408,   666,
      88,  -223,  -223,    51,    69,   -23,  -223,  -223,  -223,  -223,
      42,  -223,   542,  -223,  1101,  1055,  1055,  1004,  -223,    72,
    1055,   -12,  -223,  -223,   785,   806,   806,   830,    17,   123,
     129,   132,   524,   141,   109,   127,   134,   559,   645,  -223,
    -223,  -223,  -223,  -223,  -223,  -223,  -223,  -223,   192,   274,
     830,  -223,   121,    36,   224,   116,   229,   151,   150,   158,
     236,    -2,  -223,  -223,    43,  -223,  -223,  -223,   348,   418,
    -223,  -223,  -223,  -223,   164,  -223,  -223,  -223,  -223,    18,
     198,   188,  -223,    16,  -223,  -223,  -223,  -223,   197,   -15,
     830,    51,  -223,  -223,   542,  -223,  -223,  -223,  1024,  -223,
    -223,  -223,   830,    76,  -223,   184,  -223,   524,   645,  -223,
     830,  -223,  -223,   190,   524,   830,   830,   830,   217,   596,
     191,  -223,  -223,  -223,   114,    49,    85,   212,   273,  -223,
    -223,   690,   830,   275,  -223,  -223,  -223,  -223,  -223,  -223,
    -223,  -223,  -223,  -223,  -223,   830,  -223,   830,   830,   830,
     830,   830,   830,   830,   830,   830,   830,   830,   830,   830,
     830,   830,   830,   830,   830,   830,   830,  -223,  -223,   454,
    -223,  -223,   924,   715,  -223,    22,  -223,   165,  -223,  1233,
    -223,   282,  -223,  -223,  -223,  -223,  -223,    35,  -223,  -223,
      72,  -223,   830,  -223,   215,   524,  -223,    81,   120,   145,
     227,   596,  -223,  -223,  -223,  1157,   170,  -223,   830,  -223,
    -223,   146,  -223,     1,  -223,  -223,  -223,  -223,  -223,   121,
     121,    36,    36,   224,   224,   224,   224,   116,   116,   229,
     151,   150,   158,   236,   -50,  -223,  -223,  -223,   228,   240,
    -223,   225,   165,  1198,   736,  -223,  -223,  -223,   488,  -223,
    -223,  -223,  -223,  -223,   524,   524,   524,   830,   760,  -223,
    -223,   830,  -223,   830,  -223,  -223,  -223,  -223,   242,  -223,
     241,  -223,  -223,   239,  -223,  -223,   148,   524,   155,  -223,
    -223,  -223,  -223,   524,   244,  -223,   524,  -223,  -223,  -223
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,   133,   104,    88,    89,    90,    91,    92,    94,    95,
      96,    97,   100,   101,    98,    99,   129,   130,    93,   108,
     109,     0,     0,   140,   208,     0,    78,    80,   102,     0,
     103,    82,     0,   132,     0,     0,   205,   207,   124,     0,
       0,   144,   142,   141,    76,     0,    84,    86,    79,    81,
     107,     0,    83,     0,   187,     0,   212,     0,     0,     0,
     131,     1,   206,     0,   127,     0,   125,   134,   145,   143,
       0,    77,     0,   210,     0,     0,   114,     0,   110,     0,
     116,     2,     3,     4,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    22,
      23,    24,    25,    26,    27,   191,   183,     6,    16,    28,
       0,    30,    34,    37,    40,    45,    48,    50,    52,    54,
      56,    58,    60,    73,     0,   189,   174,   175,     0,     0,
     176,   177,   178,   179,    86,   188,   211,   153,   139,   152,
       0,   146,   148,     0,     2,   136,    28,    75,     0,     0,
       0,     0,   122,    85,     0,   169,    87,   209,     0,   113,
     106,   111,     0,     0,   117,   119,   115,     0,     0,    20,
       0,    17,    18,     0,     0,     0,     0,     0,     0,     0,
       0,   201,   202,   203,     0,     0,   155,     0,     0,    12,
      13,     0,     0,     0,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    62,     0,    19,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   192,   185,     0,
     184,   190,     0,     0,   150,   157,   151,   158,   137,     0,
     138,     0,   135,   123,   128,   126,   172,     0,   105,   120,
       0,   112,     0,   180,     0,     0,   182,     0,     0,     0,
       0,     0,   200,   204,     5,     0,   157,   156,     0,    11,
       8,     0,    14,     0,    10,    61,    31,    32,    33,    35,
      36,    38,    39,    43,    44,    41,    42,    46,    47,    49,
      51,    53,    55,    57,     0,    74,   186,   165,     0,     0,
     161,     0,   159,     0,     0,   147,   149,   154,     0,   170,
     118,   121,    21,   181,     0,     0,     0,     0,     0,    29,
       9,     0,     7,     0,   166,   160,   162,   167,     0,   163,
       0,   171,   173,   193,   195,   196,     0,     0,     0,    15,
      59,   168,   164,     0,     0,   198,     0,   194,   197,   199
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -223,  -223,  -223,  -223,   -48,  -223,   -91,    37,    46,     8,
      48,   110,   119,   122,   118,   135,  -223,   -55,   -70,  -223,
     -38,   -54,     6,     0,  -223,   272,  -223,   -27,  -223,  -223,
     268,   -67,   -24,  -223,   108,  -223,   300,   213,    47,   -13,
     -29,    -3,  -223,   -57,  -223,   126,  -223,   199,  -122,  -222,
    -151,  -223,   -74,  -223,   156,   -25,   238,  -172,  -223,  -223,
    -223,  -223,   333,  -223
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,   107,   108,   271,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   205,
     124,   148,    54,    55,    45,    46,    26,    27,    28,    29,
      77,    78,    79,   163,   164,    30,    65,    66,    31,    32,
      33,    34,    43,   298,   141,   142,   143,   187,   299,   237,
     156,   247,   125,   126,   127,    57,   129,   130,   131,   132,
     133,    35,    36,    37
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      25,   140,   155,   246,   147,    60,    24,   261,    38,    40,
     161,   146,    47,   302,    50,   224,   226,   236,   178,   206,
      42,     1,    74,    63,    76,     1,    48,    49,   128,     1,
     323,    52,   147,   173,     1,    25,   169,   171,   172,   146,
      69,    24,   134,   151,   302,     1,    16,    17,    76,    76,
      76,   151,   159,    76,    64,   231,   166,   134,   139,   184,
     185,   152,   146,   135,   267,   322,   165,   226,   167,   243,
      41,    76,    23,    75,   186,     1,    67,   225,   240,   232,
     135,   233,   241,   232,   155,   233,    23,    22,    39,   318,
      68,   161,    22,   253,    51,   147,   244,   174,    80,    23,
     256,   308,   146,    22,    70,   210,   211,   147,   249,   226,
      23,   264,   180,    44,   146,   226,   276,   277,   278,   309,
      71,   272,    80,    80,    80,   227,   234,    80,   214,   215,
     185,    76,   185,    22,   135,   275,   235,   257,   258,   259,
      23,    76,   250,   314,   186,    80,   265,   226,   233,    58,
     150,    59,   162,    23,   273,   231,   295,   332,   251,   146,
     146,   146,   146,   146,   146,   146,   146,   146,   146,   146,
     146,   146,   146,   146,   146,   146,   146,   319,   147,   301,
     226,   313,   315,   266,   175,   146,   226,   294,    56,   207,
     176,   216,   217,   177,   208,   209,   263,   147,   311,   188,
     189,   190,   179,    73,   146,    80,    60,   316,   320,   181,
     344,   226,   321,   136,   226,    80,   182,   346,   220,    40,
     146,   226,   283,   284,   285,   286,   303,   221,   304,   235,
     157,   265,   139,   233,   212,   213,   222,   165,   155,   139,
     333,   334,   335,   218,   219,    72,   328,   279,   280,   147,
     330,   339,   223,   191,   239,   192,   146,   193,   281,   282,
     238,   242,   266,   345,   252,   139,   287,   288,   340,   347,
     255,   260,   349,   262,   268,   146,   269,   312,   274,   336,
     338,    81,    82,    83,    84,   307,    85,    86,   317,   326,
     324,   343,   194,   195,   196,   197,   198,   199,   200,   201,
     202,   203,   325,   139,   341,   342,     2,     3,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,   348,    87,    88,    89,
     289,    90,    91,    92,    93,    94,    95,    96,    97,    98,
     290,   292,   153,   158,   291,    99,   100,   101,   102,   103,
     104,    81,    82,    83,    84,   204,    85,    86,   310,   293,
     105,    53,   106,   149,   245,   306,   229,   254,    62,     0,
       0,     0,     0,     0,     0,     0,     2,     3,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,     0,    87,    88,    89,
       0,    90,    91,    92,    93,    94,    95,    96,    97,    98,
       0,   137,     0,     0,     0,    99,   100,   101,   102,   103,
     104,    81,    82,    83,    84,     0,    85,    86,     0,     0,
     105,    53,   228,     0,     0,     0,     2,     3,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,     0,    81,    82,    83,
      84,     0,    85,    86,     0,     0,     0,    87,    88,    89,
     138,    90,    91,    92,    93,    94,    95,    96,    97,    98,
       0,     0,     0,     0,     0,    99,   100,   101,   102,   103,
     104,   144,    82,    83,    84,     0,    85,    86,     0,     0,
     105,    53,   230,    87,    88,    89,     0,    90,    91,    92,
      93,    94,    95,    96,    97,    98,     0,     0,     0,     0,
       0,    99,   100,   101,   102,   103,   104,    81,    82,    83,
      84,     0,    85,    86,     0,     0,   105,    53,   296,     0,
       0,     0,     0,     0,     0,   144,    82,    83,    84,    98,
      85,    86,     0,     0,     0,    99,   100,   101,   102,   103,
     104,     0,   144,    82,    83,    84,     0,    85,    86,     0,
       0,   154,   331,    87,    88,    89,     0,    90,    91,    92,
      93,    94,    95,    96,    97,    98,     0,     0,     0,     0,
       0,    99,   100,   101,   102,   103,   104,     0,     0,   144,
      82,    83,    84,    98,    85,    86,   105,    53,     0,    99,
     100,   101,   102,   103,   104,     0,     0,     0,     0,     0,
      98,     0,     0,     0,     0,   154,    99,   100,   101,   102,
     103,   104,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   183,     0,     0,     0,     0,     0,     0,   144,    82,
      83,    84,     0,    85,    86,     0,     0,    98,     0,     0,
       0,     0,     0,    99,   100,   101,   102,   103,   104,   144,
      82,    83,    84,     2,    85,    86,     0,     0,   105,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,   144,    82,    83,    84,     0,    85,    86,
       0,     0,     0,     0,     0,     0,    98,     0,     0,     0,
       0,     0,    99,   100,   101,   102,   103,   104,   144,    82,
      83,    84,     0,    85,    86,     0,     0,    98,     0,     0,
     145,     0,     0,    99,   100,   101,   102,   103,   104,   144,
      82,    83,    84,     0,    85,    86,     0,     0,     0,     0,
       0,    98,   270,     0,     0,     0,     0,    99,   100,   101,
     102,   103,   104,   144,    82,    83,    84,     0,    85,    86,
       0,     0,     0,     0,     0,     0,    98,     0,     0,   300,
       0,     0,    99,   100,   101,   102,   103,   104,   144,    82,
      83,    84,     0,    85,    86,     0,     0,    98,     0,     0,
     329,     0,     0,    99,   100,   101,   102,   103,   104,   144,
      82,    83,    84,     0,    85,    86,     0,     0,     0,     0,
       0,    98,   337,     0,     0,     0,     0,    99,   100,   101,
     102,   103,   104,   144,    82,    83,    84,     0,    85,    86,
       0,     0,     0,     0,     0,     0,   168,     0,     0,     0,
       0,     0,    99,   100,   101,   102,   103,   104,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   170,     0,     0,
       0,     0,     0,    99,   100,   101,   102,   103,   104,    61,
       0,     0,     1,     0,     0,     0,     0,     0,     0,     0,
       0,    98,     0,     0,     0,     0,     0,    99,   100,   101,
     102,   103,   104,     0,     0,     0,     0,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,     1,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      22,     0,     0,     0,     0,     0,     0,    23,     0,     0,
       0,     0,     2,     3,     4,     5,     6,     7,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,     1,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   232,   297,   233,     0,     0,
       0,     0,    23,     0,     0,     0,     0,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      22,     0,     2,     0,     0,     0,     0,    23,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,     2,     0,     0,     0,     0,     0,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     2,     0,     0,     0,     0,   160,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,     0,     0,     0,     0,     0,   248,     2,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,     2,
       3,     4,     5,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    72,     0,    53,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    53,     2,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   265,   297,
     233,     0,     0,     0,     0,    23,     2,     3,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     327,     2,     3,     4,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,   305,     2,     3,     4,     5,     6,     7,     8,     9,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21
};

static const yytype_int16 yycheck[] =
{
       0,    58,    72,   154,    59,    34,     0,   179,     3,    22,
      77,    59,    25,   235,     3,    17,    66,   139,    92,   110,
      23,     3,    47,    83,    51,     3,    26,    27,    53,     3,
      80,    31,    87,    87,     3,    35,    84,    85,    86,    87,
      43,    35,    55,    66,   266,     3,    42,    43,    75,    76,
      77,    66,    76,    80,     3,   129,    80,    70,    58,    97,
      98,    84,   110,    57,   186,    64,    79,    66,    80,    84,
      23,    98,    68,    83,    98,     3,    62,    79,    62,    61,
      74,    63,    66,    61,   154,    63,    68,    61,    83,   261,
      43,   158,    61,   167,    83,   150,   150,    80,    51,    68,
     174,    66,   150,    61,    66,    69,    70,   162,   162,    66,
      68,    62,     3,    82,   162,    66,   207,   208,   209,    84,
      82,   191,    75,    76,    77,    82,   139,    80,    12,    13,
     168,   158,   170,    61,   128,   205,   139,   175,   176,   177,
      68,   168,    66,    62,   168,    98,    61,    66,    63,    61,
      81,    63,    80,    68,   192,   229,   226,   308,    82,   207,
     208,   209,   210,   211,   212,   213,   214,   215,   216,   217,
     218,   219,   220,   221,   222,   223,   224,   268,   233,   233,
      66,   255,    62,   186,    61,   233,    66,   225,    32,    68,
      61,    75,    76,    61,    73,    74,    82,   252,   252,     7,
       8,     9,    61,    47,   252,   158,   235,    62,    62,    82,
      62,    66,    66,    57,    66,   168,    82,    62,    67,   232,
     268,    66,   214,   215,   216,   217,    61,    77,    63,   232,
      74,    61,   232,    63,    10,    11,    78,   250,   308,   239,
     314,   315,   316,    14,    15,    81,   303,   210,   211,   304,
     304,   321,    16,    61,    66,    63,   304,    65,   212,   213,
      62,    64,   265,   337,    80,   265,   218,   219,   323,   343,
      80,    54,   346,    82,    62,   323,     3,    62,     3,   317,
     318,     3,     4,     5,     6,     3,     8,     9,    61,    64,
      62,    52,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    62,   303,    62,    64,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    82,    49,    50,    51,
     220,    53,    54,    55,    56,    57,    58,    59,    60,    61,
     221,   223,    70,    75,   222,    67,    68,    69,    70,    71,
      72,     3,     4,     5,     6,    81,     8,     9,   250,   224,
      82,    83,    84,    63,   151,   239,   128,   168,    35,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    -1,    49,    50,    51,
      -1,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      -1,     3,    -1,    -1,    -1,    67,    68,    69,    70,    71,
      72,     3,     4,     5,     6,    -1,     8,     9,    -1,    -1,
      82,    83,    84,    -1,    -1,    -1,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    -1,     3,     4,     5,
       6,    -1,     8,     9,    -1,    -1,    -1,    49,    50,    51,
      62,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      -1,    -1,    -1,    -1,    -1,    67,    68,    69,    70,    71,
      72,     3,     4,     5,     6,    -1,     8,     9,    -1,    -1,
      82,    83,    84,    49,    50,    51,    -1,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    -1,    -1,    -1,    -1,
      -1,    67,    68,    69,    70,    71,    72,     3,     4,     5,
       6,    -1,     8,     9,    -1,    -1,    82,    83,    84,    -1,
      -1,    -1,    -1,    -1,    -1,     3,     4,     5,     6,    61,
       8,     9,    -1,    -1,    -1,    67,    68,    69,    70,    71,
      72,    -1,     3,     4,     5,     6,    -1,     8,     9,    -1,
      -1,    83,    84,    49,    50,    51,    -1,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    -1,    -1,    -1,    -1,
      -1,    67,    68,    69,    70,    71,    72,    -1,    -1,     3,
       4,     5,     6,    61,     8,     9,    82,    83,    -1,    67,
      68,    69,    70,    71,    72,    -1,    -1,    -1,    -1,    -1,
      61,    -1,    -1,    -1,    -1,    83,    67,    68,    69,    70,
      71,    72,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    82,    -1,    -1,    -1,    -1,    -1,    -1,     3,     4,
       5,     6,    -1,     8,     9,    -1,    -1,    61,    -1,    -1,
      -1,    -1,    -1,    67,    68,    69,    70,    71,    72,     3,
       4,     5,     6,    28,     8,     9,    -1,    -1,    82,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,     3,     4,     5,     6,    -1,     8,     9,
      -1,    -1,    -1,    -1,    -1,    -1,    61,    -1,    -1,    -1,
      -1,    -1,    67,    68,    69,    70,    71,    72,     3,     4,
       5,     6,    -1,     8,     9,    -1,    -1,    61,    -1,    -1,
      64,    -1,    -1,    67,    68,    69,    70,    71,    72,     3,
       4,     5,     6,    -1,     8,     9,    -1,    -1,    -1,    -1,
      -1,    61,    62,    -1,    -1,    -1,    -1,    67,    68,    69,
      70,    71,    72,     3,     4,     5,     6,    -1,     8,     9,
      -1,    -1,    -1,    -1,    -1,    -1,    61,    -1,    -1,    64,
      -1,    -1,    67,    68,    69,    70,    71,    72,     3,     4,
       5,     6,    -1,     8,     9,    -1,    -1,    61,    -1,    -1,
      64,    -1,    -1,    67,    68,    69,    70,    71,    72,     3,
       4,     5,     6,    -1,     8,     9,    -1,    -1,    -1,    -1,
      -1,    61,    62,    -1,    -1,    -1,    -1,    67,    68,    69,
      70,    71,    72,     3,     4,     5,     6,    -1,     8,     9,
      -1,    -1,    -1,    -1,    -1,    -1,    61,    -1,    -1,    -1,
      -1,    -1,    67,    68,    69,    70,    71,    72,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    61,    -1,    -1,
      -1,    -1,    -1,    67,    68,    69,    70,    71,    72,     0,
      -1,    -1,     3,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    61,    -1,    -1,    -1,    -1,    -1,    67,    68,    69,
      70,    71,    72,    -1,    -1,    -1,    -1,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,     3,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      61,    -1,    -1,    -1,    -1,    -1,    -1,    68,    -1,    -1,
      -1,    -1,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,     3,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    61,    62,    63,    -1,    -1,
      -1,    -1,    68,    -1,    -1,    -1,    -1,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      61,    -1,    28,    -1,    -1,    -1,    -1,    68,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,    28,    -1,    -1,    -1,    -1,    -1,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    28,    -1,    -1,    -1,    -1,    84,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    -1,    -1,    -1,    -1,    -1,    84,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    47,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    47,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    81,    -1,    83,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    83,    28,    29,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    61,    62,
      63,    -1,    -1,    -1,    -1,    68,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      62,    28,    29,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     3,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,    61,    68,   107,   108,   111,   112,   113,   114,
     120,   123,   124,   125,   126,   146,   147,   148,     3,    83,
     124,   123,   126,   127,    82,   109,   110,   124,   108,   108,
       3,    83,   108,    83,   107,   108,   139,   140,    61,    63,
     125,     0,   147,    83,     3,   121,   122,    62,   123,   126,
      66,    82,    81,   139,   140,    83,   112,   115,   116,   117,
     123,     3,     4,     5,     6,     8,     9,    49,    50,    51,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    67,
      68,    69,    70,    71,    72,    82,    84,    86,    87,    89,
      90,    91,    92,    93,    94,    95,    96,    97,    98,    99,
     100,   101,   102,   103,   105,   137,   138,   139,   140,   141,
     142,   143,   144,   145,   124,   107,   139,     3,    62,   108,
     128,   129,   130,   131,     3,    64,    89,   102,   106,   121,
      81,    66,    84,   110,    83,   103,   135,   139,   115,   117,
      84,   116,    80,   118,   119,   124,   117,    80,    61,    89,
      61,    89,    89,   106,    80,    61,    61,    61,   137,    61,
       3,    82,    82,    82,   105,   105,   117,   132,     7,     8,
       9,    61,    63,    65,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    81,   104,    91,    68,    73,    74,
      69,    70,    10,    11,    12,    13,    75,    76,    14,    15,
      67,    77,    78,    16,    17,    79,    66,    82,    84,   141,
      84,   137,    61,    63,   124,   126,   133,   134,    62,    66,
      62,    66,    64,    84,   106,   122,   135,   136,    84,   106,
      66,    82,    80,   137,   132,    80,   137,   105,   105,   105,
      54,   142,    82,    82,    62,    61,   126,   133,    62,     3,
      62,    88,   103,   105,     3,   103,    91,    91,    91,    92,
      92,    93,    93,    94,    94,    94,    94,    95,    95,    96,
      97,    98,    99,   100,   105,   103,    84,    62,   128,   133,
      64,   106,   134,    61,    63,    48,   130,     3,    66,    84,
     119,   106,    62,   137,    62,    62,    62,    61,   142,    91,
      62,    66,    64,    80,    62,    62,    64,    62,   128,    64,
     106,    84,   135,   137,   137,   137,   105,    62,   105,   103,
     102,    62,    64,    52,    62,   137,    62,   137,    82,   137
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    85,    86,    86,    86,    86,    87,    87,    87,    87,
      87,    87,    87,    87,    88,    88,    89,    89,    89,    89,
      89,    89,    90,    90,    90,    90,    90,    90,    91,    91,
      92,    92,    92,    92,    93,    93,    93,    94,    94,    94,
      95,    95,    95,    95,    95,    96,    96,    96,    97,    97,
      98,    98,    99,    99,   100,   100,   101,   101,   102,   102,
     103,   103,   104,   104,   104,   104,   104,   104,   104,   104,
     104,   104,   104,   105,   105,   106,   107,   107,   108,   108,
     108,   108,   108,   108,   109,   109,   110,   110,   111,   111,
     111,   111,   111,   112,   112,   112,   112,   112,   112,   112,
     112,   112,   112,   112,   112,   113,   113,   113,   114,   114,
     115,   115,   116,   117,   117,   117,   117,   118,   118,   119,
     119,   119,   120,   120,   120,   121,   121,   122,   122,   123,
     123,   124,   124,   125,   125,   125,   125,   125,   125,   125,
     126,   126,   126,   126,   127,   127,   128,   128,   129,   129,
     130,   130,   130,   131,   131,   132,   132,   133,   133,   133,
     134,   134,   134,   134,   134,   134,   134,   134,   134,   135,
     135,   135,   136,   136,   137,   137,   137,   137,   137,   137,
     138,   138,   138,   139,   139,   139,   139,   140,   140,   141,
     141,   142,   142,   143,   143,   143,   144,   144,   144,   144,
     145,   145,   145,   145,   145,   146,   146,   147,   147,   148,
     148,   148,   148
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     1,     3,     1,     4,     3,     4,
       3,     3,     2,     2,     1,     3,     1,     2,     2,     2,
       2,     4,     1,     1,     1,     1,     1,     1,     1,     4,
       1,     3,     3,     3,     1,     3,     3,     1,     3,     3,
       1,     3,     3,     3,     3,     1,     3,     3,     1,     3,
       1,     3,     1,     3,     1,     3,     1,     3,     1,     5,
       1,     3,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     3,     1,     2,     3,     1,     2,
       1,     2,     1,     2,     1,     3,     1,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     5,     4,     2,     1,     1,
       1,     2,     3,     2,     1,     2,     1,     1,     3,     1,
       2,     3,     4,     5,     2,     1,     3,     1,     3,     1,
       1,     2,     1,     1,     3,     4,     3,     4,     4,     3,
       1,     2,     2,     3,     1,     2,     1,     3,     1,     3,
       2,     2,     1,     1,     3,     1,     2,     1,     1,     2,
       3,     2,     3,     3,     4,     2,     3,     3,     4,     1,
       3,     4,     1,     3,     1,     1,     1,     1,     1,     1,
       3,     4,     3,     2,     3,     3,     4,     1,     2,     1,
       2,     1,     2,     5,     7,     5,     5,     7,     6,     7,
       3,     2,     2,     2,     3,     1,     2,     1,     1,     4,
       3,     3,     2
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
#if C89_DEBUG

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
# if defined C89_LTYPE_IS_TRIVIAL && C89_LTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  unsigned res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
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
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, uscxml::C89Parser* ctx, void * scanner)
{
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
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, uscxml::C89Parser* ctx, void * scanner)
{
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
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
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
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, uscxml::C89Parser* ctx, void * scanner)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
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
#else /* !C89_DEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !C89_DEBUG */


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
yystrlen (const char *yystr)
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
static char *
yystpcpy (char *yydest, const char *yysrc)
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
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
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

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, uscxml::C89Parser* ctx, void * scanner)
{
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
yyparse (uscxml::C89Parser* ctx, void * scanner)
{
/* The lookahead symbol.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

/* Location data for the lookahead symbol.  */
static YYLTYPE yyloc_default
# if defined C89_LTYPE_IS_TRIVIAL && C89_LTYPE_IS_TRIVIAL
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
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex (&yylval, &yylloc, scanner);
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
  switch (yyn)
    {
        case 2:
#line 79 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->value(IDENTIFIER, (void*)&((yylsp[0])), (yyvsp[0].value)); free((yyvsp[0].value)); 
	}
#line 1888 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 3:
#line 82 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->value(CONSTANT, (void*)&((yylsp[0])), (yyvsp[0].value)); free((yyvsp[0].value));
	}
#line 1896 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 4:
#line 85 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->value(STRING_LITERAL, (void*)&((yylsp[0])), (yyvsp[0].value)); free((yyvsp[0].value));
	}
#line 1904 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 5:
#line 88 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = (yyvsp[-1].node);
	}
#line 1912 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 6:
#line 94 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = (yyvsp[0].node);
	}
#line 1920 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 7:
#line 97 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node));
	}
#line 1928 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 8:
#line 100 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-2].node));
	}
#line 1936 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 9:
#line 103 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node));
	}
#line 1944 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 10:
#line 106 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].value));
	}
#line 1952 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 11:
#line 109 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(PTR_OP, 2, (yyvsp[-2].node), (yyvsp[0].value));
	}
#line 1960 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 12:
#line 112 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(INC_OP, 1, (yyvsp[-1].node));
	}
#line 1968 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 13:
#line 115 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(DEC_OP, 1, (yyvsp[-1].node));
	}
#line 1976 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 14:
#line 121 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = (yyvsp[0].node); 
	}
#line 1984 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 15:
#line 124 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 1992 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 16:
#line 130 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = (yyvsp[0].node);
	}
#line 2000 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 17:
#line 133 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(INC_OP, 1, (yyvsp[0].node));
	}
#line 2008 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 18:
#line 136 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(DEC_OP, 1, (yyvsp[0].node));
	}
#line 2016 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 19:
#line 139 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 2024 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 20:
#line 142 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(SIZEOF, 1, (yyvsp[0].node));
	}
#line 2032 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 21:
#line 145 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(SIZEOF, 1, (yyvsp[-1].node));
	}
#line 2040 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 22:
#line 151 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2046 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 23:
#line 152 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2052 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 24:
#line 153 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2058 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 25:
#line 154 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2064 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 26:
#line 155 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2070 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 27:
#line 156 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2076 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 28:
#line 160 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2082 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 29:
#line 161 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); }
#line 2088 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 30:
#line 165 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2094 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 31:
#line 166 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2102 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 32:
#line 169 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2110 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 33:
#line 172 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2118 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 34:
#line 178 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2124 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 35:
#line 179 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2132 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 36:
#line 182 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2140 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 37:
#line 188 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2146 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 38:
#line 189 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(LEFT_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2154 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 39:
#line 192 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(RIGHT_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2162 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 40:
#line 198 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2168 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 41:
#line 199 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2176 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 42:
#line 202 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2184 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 43:
#line 205 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(LE_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2192 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 44:
#line 208 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(GE_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2200 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 45:
#line 214 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2206 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 46:
#line 215 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(EQ_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2214 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 47:
#line 218 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(NE_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2222 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 48:
#line 224 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2228 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 49:
#line 225 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2236 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 50:
#line 231 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2242 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 51:
#line 232 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2250 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 52:
#line 238 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2256 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 53:
#line 239 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2264 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 54:
#line 245 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2270 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 55:
#line 246 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(AND_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2278 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 56:
#line 252 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2284 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 57:
#line 253 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(OR_OP, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2292 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 58:
#line 259 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2298 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 59:
#line 260 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 3, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2306 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 60:
#line 266 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2312 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 61:
#line 267 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2320 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 62:
#line 273 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node('=', 0); }
#line 2326 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 63:
#line 274 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(MUL_ASSIGN, 0); }
#line 2332 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 64:
#line 275 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(DIV_ASSIGN, 0); }
#line 2338 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 65:
#line 276 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(MOD_ASSIGN, 0); }
#line 2344 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 66:
#line 277 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(ADD_ASSIGN, 0); }
#line 2350 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 67:
#line 278 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(SUB_ASSIGN, 0); }
#line 2356 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 68:
#line 279 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(LEFT_ASSIGN, 0); }
#line 2362 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 69:
#line 280 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(RIGHT_ASSIGN, 0); }
#line 2368 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 70:
#line 281 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(AND_ASSIGN, 0); }
#line 2374 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 71:
#line 282 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(XOR_ASSIGN, 0); }
#line 2380 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 72:
#line 283 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(OR_ASSIGN, 0); }
#line 2386 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 73:
#line 287 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2392 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 74:
#line 288 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2400 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 75:
#line 294 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2406 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 76:
#line 298 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2412 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 77:
#line 299 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[-1].node)); 
	}
#line 2420 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 78:
#line 305 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2426 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 79:
#line 306 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 2434 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 80:
#line 309 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2440 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 81:
#line 310 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 2448 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 82:
#line 313 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2454 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 83:
#line 314 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 2462 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 84:
#line 320 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2468 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 85:
#line 321 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 2476 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 86:
#line 327 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2482 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 87:
#line 328 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 2490 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 88:
#line 334 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(TYPEDEF, 0); }
#line 2496 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 89:
#line 335 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(EXTERN, 0); }
#line 2502 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 90:
#line 336 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(STATIC, 0); }
#line 2508 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 91:
#line 337 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(AUTO, 0); }
#line 2514 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 92:
#line 338 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(REGISTER, 0); }
#line 2520 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 93:
#line 342 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(VOID, 0); }
#line 2526 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 94:
#line 343 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(CHAR, 0); }
#line 2532 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 95:
#line 344 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(SHORT, 0); }
#line 2538 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 96:
#line 345 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(INT, 0); }
#line 2544 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 97:
#line 346 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(LONG, 0); }
#line 2550 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 98:
#line 347 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(FLOAT, 0); }
#line 2556 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 99:
#line 348 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(DOUBLE, 0); }
#line 2562 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 100:
#line 349 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(SIGNED, 0); }
#line 2568 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 101:
#line 350 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(UNSIGNED, 0); }
#line 2574 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 102:
#line 351 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2580 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 103:
#line 352 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2586 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 104:
#line 353 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(TYPE_NAME, 0); }
#line 2592 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 105:
#line 357 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 3, (yyvsp[-4].node), (yyvsp[-3].value), (yyvsp[-1].node));
	}
#line 2600 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 106:
#line 360 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node));
	}
#line 2608 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 107:
#line 363 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-1].node));	
	}
#line 2616 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 108:
#line 369 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(STRUCT, 0); }
#line 2622 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 109:
#line 370 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(STRUCT, 1); }
#line 2628 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 110:
#line 374 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2634 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 111:
#line 375 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-1].node), (yyvsp[0].node)); 
	}
#line 2642 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 112:
#line 381 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[-1].node)); 
	}
#line 2650 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 113:
#line 387 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(',', 2, (yyvsp[-1].node), (yyvsp[0].node)); 
	}
#line 2658 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 114:
#line 390 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2664 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 115:
#line 391 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node)); 
	}
#line 2672 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 116:
#line 394 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2678 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 117:
#line 398 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2684 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 118:
#line 399 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 2692 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 119:
#line 405 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2698 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 120:
#line 406 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 1, (yyvsp[0].node)); 
	}
#line 2706 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 121:
#line 409 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 2714 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 122:
#line 415 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(ENUM, 1, (yyvsp[-1].node)); }
#line 2720 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 123:
#line 416 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(ENUM, 2, (yyvsp[-3].value), (yyvsp[-1].node)); }
#line 2726 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 124:
#line 417 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(ENUM, 1, (yyvsp[0].value)); }
#line 2732 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 125:
#line 421 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2738 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 126:
#line 422 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 2746 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 127:
#line 428 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->value(IDENTIFIER, (void*)&((yylsp[0])), (yyvsp[0].value)); free((yyvsp[0].value));	
	}
#line 2754 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 128:
#line 431 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 2, (yyvsp[-2].value), (yyvsp[0].node)); }
#line 2760 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 129:
#line 435 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2766 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 130:
#line 436 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2772 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 131:
#line 440 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node)); 
	}
#line 2780 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 132:
#line 443 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2786 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 133:
#line 447 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->value(IDENTIFIER, (void*)&((yylsp[0])), (yyvsp[0].value)); free((yyvsp[0].value));
	}
#line 2794 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 134:
#line 450 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 1, (yyvsp[-1].node)); 
	}
#line 2802 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 135:
#line 453 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node)); 	
	}
#line 2810 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 136:
#line 456 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-2].node));
	}
#line 2818 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 137:
#line 459 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node)); 	
	}
#line 2826 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 138:
#line 462 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node));
	}
#line 2834 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 139:
#line 465 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-2].node)); 	
	}
#line 2842 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 140:
#line 471 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2848 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 141:
#line 472 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 1, (yyvsp[0].node)); }
#line 2854 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 142:
#line 473 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 1, (yyvsp[0].node)); }
#line 2860 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 143:
#line 474 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node)); }
#line 2866 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 144:
#line 478 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2872 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 145:
#line 479 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 2880 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 146:
#line 486 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2886 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 147:
#line 487 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(ELLIPSIS, 1, (yyvsp[-2].node)); }
#line 2892 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 148:
#line 491 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2898 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 149:
#line 492 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[0].node)); 
	}
#line 2906 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 150:
#line 498 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node)); 
	}
#line 2914 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 151:
#line 501 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node)); 
	}
#line 2922 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 152:
#line 504 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2928 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 153:
#line 508 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->value(IDENTIFIER, (void*)&((yylsp[0])), (yyvsp[0].value)); free((yyvsp[0].value));
	}
#line 2936 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 154:
#line 511 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].value)); 
	}
#line 2944 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 155:
#line 517 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2950 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 156:
#line 518 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 2958 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 157:
#line 524 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2964 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 158:
#line 525 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 2970 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 159:
#line 526 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2976 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 160:
#line 530 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2982 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 161:
#line 531 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 2988 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 162:
#line 532 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-1].node); }
#line 2994 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 163:
#line 533 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[-2].node); }
#line 3000 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 164:
#line 534 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node)); 
	}
#line 3008 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 165:
#line 537 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 0); }
#line 3014 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 166:
#line 538 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 1, (yyvsp[-1].node)); }
#line 3020 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 167:
#line 539 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 1, (yyvsp[-2].node)); }
#line 3026 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 168:
#line 540 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 2, (yyvsp[-3].node), (yyvsp[-1].node)); 
	}
#line 3034 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 169:
#line 546 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3040 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 170:
#line 547 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-1].node));
	}
#line 3048 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 171:
#line 550 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-2].node));
	}
#line 3056 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 172:
#line 556 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3062 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 173:
#line 557 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 3070 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 174:
#line 563 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3076 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 175:
#line 564 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3082 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 176:
#line 565 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3088 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 177:
#line 566 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3094 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 178:
#line 567 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3100 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 179:
#line 568 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3106 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 180:
#line 572 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(IDENTIFIER, 2, (yyvsp[-2].value), (yyvsp[0].node)); 
	}
#line 3114 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 181:
#line 575 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(CASE, 2, (yyvsp[-2].node), (yyvsp[0].node)); 	
	}
#line 3122 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 182:
#line 578 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(DEFAULT, 1, (yyvsp[0].node)); 	
	}
#line 3130 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 183:
#line 584 "c89.ypp" /* yacc.c:1646  */
    { 
		(yyval.node) = ctx->node(0, 0); 
	}
#line 3138 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 184:
#line 587 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-1].node));
	}
#line 3146 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 185:
#line 590 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 1, (yyvsp[-1].node));
	}
#line 3154 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 186:
#line 593 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-2].node), (yyvsp[-1].node)); 		
	}
#line 3162 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 187:
#line 599 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3168 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 188:
#line 600 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 3176 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 189:
#line 606 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3182 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 190:
#line 607 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(',', 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 3190 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 191:
#line 613 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 0); 
	}
#line 3198 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 192:
#line 616 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = (yyvsp[-1].node);
	}
#line 3206 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 193:
#line 622 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(IF, 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 3214 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 194:
#line 625 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(IF, 3, (yyvsp[-4].node), (yyvsp[-2].node), (yyvsp[0].node));	
	}
#line 3222 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 195:
#line 628 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(SWITCH, 2, (yyvsp[-2].node), (yyvsp[0].node));	
	}
#line 3230 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 196:
#line 634 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(WHILE, 2, (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 3238 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 197:
#line 637 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(DO, 2, (yyvsp[-2].node), (yyvsp[-5].node));	
	}
#line 3246 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 198:
#line 640 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(FOR, 3, (yyvsp[-3].node), (yyvsp[-2].node), (yyvsp[0].node));	
	}
#line 3254 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 199:
#line 643 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(FOR, 4, (yyvsp[-4].node), (yyvsp[-3].node), (yyvsp[-2].node), (yyvsp[0].node));
	}
#line 3262 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 200:
#line 649 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(GOTO, 1, (yyvsp[-1].value)); }
#line 3268 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 201:
#line 650 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(CONTINUE, 0); }
#line 3274 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 202:
#line 651 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(BREAK, 0); }
#line 3280 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 203:
#line 652 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(RETURN, 0); }
#line 3286 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 204:
#line 653 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(RETURN, 1, (yyvsp[-1].node)); }
#line 3292 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 205:
#line 657 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3298 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 206:
#line 658 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node)); }
#line 3304 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 207:
#line 662 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3310 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 208:
#line 663 "c89.ypp" /* yacc.c:1646  */
    { (yyval.node) = (yyvsp[0].node); }
#line 3316 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 209:
#line 667 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 4, (yyvsp[-3].node), (yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 3324 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 210:
#line 670 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 3, (yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node));	
	}
#line 3332 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 211:
#line 673 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 3, (yyvsp[-2].node), (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 3340 "c89.tab.cpp" /* yacc.c:1646  */
    break;

  case 212:
#line 676 "c89.ypp" /* yacc.c:1646  */
    {
		(yyval.node) = ctx->node(0, 2, (yyvsp[-1].node), (yyvsp[0].node));
	}
#line 3348 "c89.tab.cpp" /* yacc.c:1646  */
    break;


#line 3352 "c89.tab.cpp" /* yacc.c:1646  */
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
  if (!yyerrstatus)
    {
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
        yyerror (&yylloc, ctx, scanner, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

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
  if (yychar != YYEMPTY)
    {
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
  while (yyssp != yyss)
    {
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
#line 681 "c89.ypp" /* yacc.c:1906  */

