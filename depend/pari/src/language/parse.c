/* A Bison parser, made by GNU Bison 3.0.2.  */

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
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         pari_parse
#define yylex           pari_lex
#define yyerror         pari_error
#define yydebug         pari_debug
#define yynerrs         pari_nerrs


/* Copy the first part of user declarations.  */
#line 1 "../src/language/parse.y" /* yacc.c:339  */

/* Copyright (C) 2006  The PARI group.

This file is part of the PARI package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#define YYSIZE_T size_t
#define YYSTYPE union token_value
#define YYLTYPE struct node_loc
#define YYLLOC_DEFAULT(Current, Rhs, N)     \
        ((Current).start  = ((N)?(Rhs)[1].start:(Rhs)[0].end),  \
         (Current).end    = (Rhs)[N].end)
#include "parsec.h"
#define NOARG(x) newnode(Fnoarg,-1,-1,&(x))
#define NORANGE(x) newnode(Fnorange,-1,-1,&(x))

#line 97 "../src/language/parse.c" /* yacc.c:339  */

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
   by #include "parse.h".  */
#ifndef YY_PARI_SRC_LANGUAGE_PARSE_H_INCLUDED
# define YY_PARI_SRC_LANGUAGE_PARSE_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int pari_debug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    KPARROW = 258,
    KARROW = 259,
    KDOTDOT = 260,
    KPE = 261,
    KSE = 262,
    KME = 263,
    KDE = 264,
    KDRE = 265,
    KEUCE = 266,
    KMODE = 267,
    KAND = 268,
    KOR = 269,
    KID = 270,
    KEQ = 271,
    KNE = 272,
    KGE = 273,
    KLE = 274,
    KSRE = 275,
    KSLE = 276,
    KSR = 277,
    KSL = 278,
    KDR = 279,
    KPP = 280,
    KSS = 281,
    KINTEGER = 282,
    KREAL = 283,
    KENTRY = 284,
    KSTRING = 285,
    SEQ = 286,
    DEFFUNC = 287,
    INT = 288,
    LVAL = 289,
    SIGN = 290
  };
#endif

/* Value type.  */

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif



int pari_parse (char **lex);

#endif /* !YY_PARI_SRC_LANGUAGE_PARSE_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 192 "../src/language/parse.c" /* yacc.c:358  */

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
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

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
#define YYFINAL  47
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   671

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  61
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  21
/* YYNRULES -- Number of rules.  */
#define YYNRULES  109
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  192

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   290

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    50,     2,    49,     2,    43,    38,    53,
      55,    59,    46,    41,    36,    42,    54,    45,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    56,    35,
      40,    37,    39,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    52,    44,    57,    48,     2,    58,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    60,     2,    51,     2,     2,     2,
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
      47
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] =
{
       0,    86,    86,    89,    90,    91,    92,    95,    96,    97,
      98,   101,   102,   105,   106,   109,   110,   111,   112,   113,
     114,   117,   118,   119,   120,   122,   123,   124,   125,   126,
     127,   128,   129,   130,   131,   132,   133,   134,   135,   136,
     137,   138,   139,   140,   141,   142,   143,   144,   145,   146,
     147,   148,   149,   150,   151,   152,   153,   154,   155,   156,
     157,   158,   159,   160,   161,   162,   163,   164,   165,   166,
     167,   168,   169,   170,   171,   172,   173,   174,   177,   178,
     179,   182,   183,   186,   187,   190,   191,   192,   193,   194,
     195,   198,   201,   202,   203,   204,   207,   210,   211,   212,
     213,   213,   217,   218,   221,   224,   227,   229,   231,   232
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "\")->\"", "\"->\"", "\"..\"", "\"+=\"",
  "\"-=\"", "\"*=\"", "\"/=\"", "\"\\\\/=\"", "\"\\\\=\"", "\"%=\"",
  "\"&&\"", "\"||\"", "\"===\"", "\"==\"", "\"!=\"", "\">=\"", "\"<=\"",
  "\">>=\"", "\"<<=\"", "\">>\"", "\"<<\"", "\"\\\\/\"", "\"++\"",
  "\"--\"", "\"integer\"", "\"real number\"", "\"variable name\"",
  "\"character string\"", "SEQ", "DEFFUNC", "INT", "LVAL", "';'", "','",
  "'='", "'&'", "'>'", "'<'", "'+'", "'-'", "'%'", "'\\\\'", "'/'", "'*'",
  "SIGN", "'^'", "'#'", "'!'", "'~'", "'['", "'\\''", "'.'", "'('", "':'",
  "']'", "'`'", "')'", "'|'", "$accept", "sequence", "seq", "range",
  "matrix_index", "backticks", "history", "expr", "lvalue", "matrixelts",
  "matrixlines", "matrix", "in", "inseq", "compr", "arg", "$@1", "listarg",
  "funcid", "memberid", "definition", YY_NULLPTR
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
     285,   286,   287,   288,   289,    59,    44,    61,    38,    62,
      60,    43,    45,    37,    92,    47,    42,   290,    94,    35,
      33,   126,    91,    39,    46,    40,    58,    93,    96,    41,
     124
};
# endif

#define YYPACT_NINF -165

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-165)))

#define YYTABLE_NINF -104

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     616,   -33,  -165,   -28,  -165,   616,   616,   -17,   616,   616,
      84,     1,  -165,   582,    31,     3,  -165,   461,   141,    46,
    -165,  -165,  -165,  -165,    60,   582,   150,   150,  -165,    12,
    -165,    38,   190,    54,    42,    44,  -165,   172,    36,    47,
    -165,    61,     3,   325,   227,     6,    33,  -165,   616,   616,
     616,   616,   616,   616,   616,   616,   616,   616,   616,   616,
     616,   616,   616,   616,   616,   616,   616,   616,   616,  -165,
    -165,   599,  -165,    73,   582,    74,  -165,   616,   616,   616,
     616,   616,   616,   616,   616,   616,   616,  -165,  -165,   616,
      86,  -165,   616,  -165,   -22,  -165,    38,  -165,  -165,  -165,
     616,    61,   616,   616,  -165,   616,  -165,  -165,   -36,  -165,
     282,  -165,   616,   582,   461,   503,   503,   538,   538,   538,
     538,   538,   150,   150,   150,   503,   538,   538,   552,   552,
     150,   150,   150,   150,   150,   616,    50,   252,    79,   -19,
    -165,     3,   461,   461,   461,   461,   461,   461,   461,   461,
     461,   461,  -165,   461,    80,   372,   -27,   -12,    63,   461,
      82,   461,    82,    64,   616,     3,    32,   461,   599,  -165,
     616,   616,  -165,   616,  -165,    87,    61,   616,  -165,  -165,
     461,    65,   461,     3,     3,   616,  -165,   417,  -165,   461,
      61,  -165
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       3,    21,    22,    78,    25,     0,     0,    15,     0,     0,
       0,     0,    23,     3,     0,     2,    27,     4,    30,    31,
      32,    29,    75,    33,     0,     3,    68,    69,    16,    18,
      13,    17,    48,    47,     0,     0,    85,    81,     0,     0,
      26,     0,    97,     4,    30,     0,     0,     1,     5,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    73,
      71,     7,    72,     0,     3,     0,    74,     3,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    36,    37,     0,
       0,    79,     0,    24,     0,    19,    20,    14,    90,    87,
       0,     0,     0,     0,    88,     0,    89,    78,    99,    77,
       7,   100,     3,     3,     6,    50,    49,    52,    53,    54,
      55,    57,    62,    61,    64,    51,    56,    58,    60,    59,
      63,    65,    66,    67,    70,     0,     0,     8,   105,     0,
      76,   108,    45,    46,    38,    39,    40,    41,    42,    44,
      43,    35,    80,    34,   104,     0,     0,    92,     0,    81,
      83,    82,    84,     0,     0,   109,     0,    10,     7,    12,
       0,     3,    28,     3,    86,     0,     0,     0,    96,    98,
     101,     0,     9,   107,   106,     0,    94,    93,    11,    91,
       0,    95
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -165,  -165,    11,   -44,   -16,    99,  -165,    -5,    -7,   -83,
    -165,  -165,  -165,  -164,  -165,    18,  -165,   -10,  -165,  -165,
    -165
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    14,    42,   136,    76,    31,    16,    17,    18,    38,
      39,    19,   157,   158,    20,    45,   164,    46,    21,    22,
      23
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      26,    27,    91,    32,    33,    37,    44,   111,    43,  -102,
      28,    15,   186,   175,   113,    94,    71,   113,    44,   160,
      90,    24,   162,   176,   177,    71,   191,    25,    91,    90,
      40,    47,    29,   111,   108,  -103,   112,   154,    48,    95,
     172,    30,  -102,   114,   115,   116,   117,   118,   119,   120,
     121,   122,   123,   124,   125,   126,   127,   128,   129,   130,
     131,   132,   133,   134,   139,  -102,   137,    44,  -103,   113,
      30,   102,   103,   142,   143,   144,   145,   146,   147,   148,
     149,   150,   105,    92,   151,    34,   168,   153,   141,    93,
     107,  -103,    91,   104,   156,   155,    97,   159,   161,    98,
     159,    99,   138,   140,   106,   137,    44,   169,    73,    74,
      75,     1,     2,     3,     4,   152,   171,   173,   103,    35,
     178,   179,   188,   165,   181,     5,     6,     7,    96,   185,
     167,   166,     0,     8,     9,     0,    10,    11,    12,    13,
      91,    36,     0,     0,     0,    77,     0,    78,    79,    80,
      81,    82,    83,    84,     0,     0,     0,     0,     0,   180,
       0,    85,    86,   137,     0,   182,    87,    88,     0,   156,
       0,     0,   187,     0,     0,     0,     0,   100,    89,     0,
     189,     0,   183,   156,   184,    49,    50,    51,    52,    53,
      54,    55,     0,    71,    56,    57,    58,    90,    68,     0,
      69,    70,    71,    72,    73,    74,    75,     0,     0,     0,
      59,    60,    61,    62,    63,    64,    65,    66,    67,     0,
      68,     0,    69,    70,    71,    72,    73,    74,    75,     0,
       0,    77,   101,    78,    79,    80,    81,    82,    83,    84,
      69,    70,    71,    72,    73,    74,    75,    85,    86,     0,
       0,     0,    87,    88,     0,     0,     0,   170,     0,     0,
       0,     0,     0,     0,    89,    49,    50,    51,    52,    53,
      54,    55,     0,     0,    56,    57,    58,     0,     0,   110,
       0,     0,     0,    90,     0,     0,     0,   163,     0,     0,
      59,    60,    61,    62,    63,    64,    65,    66,    67,     0,
      68,     0,    69,    70,    71,    72,    73,    74,    75,     1,
       2,     3,     4,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     5,     6,     7,     0,     0,     0,     0,
     135,     8,     9,     0,    10,    11,    12,    13,    49,    50,
      51,    52,    53,    54,    55,     0,     0,    56,    57,    58,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    59,    60,    61,    62,    63,    64,    65,
      66,    67,     0,    68,     0,    69,    70,    71,    72,    73,
      74,    75,     0,     0,   109,    49,    50,    51,    52,    53,
      54,    55,     0,     0,    56,    57,    58,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      59,    60,    61,    62,    63,    64,    65,    66,    67,     0,
      68,     0,    69,    70,    71,    72,    73,    74,    75,   174,
      49,    50,    51,    52,    53,    54,    55,     0,     0,    56,
      57,    58,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   190,     0,     0,    59,    60,    61,    62,    63,
      64,    65,    66,    67,     0,    68,     0,    69,    70,    71,
      72,    73,    74,    75,    49,    50,    51,    52,    53,    54,
      55,     0,     0,    56,    57,    58,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    59,
      60,    61,    62,    63,    64,    65,    66,    67,     0,    68,
       0,    69,    70,    71,    72,    73,    74,    75,    51,    52,
      53,    54,    55,     0,     0,    56,    57,    58,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    60,    61,    62,    63,    64,    65,    66,    67,
       0,    68,     0,    69,    70,    71,    72,    73,    74,    75,
      56,    57,    58,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    56,    57,    58,     0,     0,    62,
      63,    64,    65,    66,    67,     0,    68,     0,    69,    70,
      71,    72,    73,    74,    75,    64,    65,    66,    67,     0,
      68,     0,    69,    70,    71,    72,    73,    74,    75,     1,
       2,     3,     4,     0,     0,     0,     0,     0,     0,     0,
      41,     0,     0,     5,     6,     7,     1,     2,     3,     4,
       0,     8,     9,     0,    10,    11,    12,    13,     0,     0,
       5,     6,     7,     1,     2,     3,     4,   135,     8,     9,
       0,    10,    11,    12,    13,     0,     0,     5,     6,     7,
       0,     0,     0,     0,     0,     8,     9,     0,    10,    11,
      12,    13
};

static const yytype_int16 yycheck[] =
{
       5,     6,    18,     8,     9,    10,    13,     1,    13,     3,
      27,     0,   176,    40,    36,    25,    52,    36,    25,   102,
      56,    54,   105,    35,    36,    52,   190,    55,    44,    56,
      29,     0,    49,     1,    41,     3,     3,    59,    35,    27,
      59,    58,    36,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    74,    59,    71,    74,    36,    36,
      58,    35,    36,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    35,    37,    89,     1,    36,    92,    77,    29,
      29,    59,   108,    57,   101,   100,    58,   102,   103,    57,
     105,    57,    29,    29,    57,   110,   113,    57,    54,    55,
      56,    27,    28,    29,    30,    29,    37,    37,    36,    35,
      57,    57,    57,   112,   168,    41,    42,    43,    29,    42,
     135,   113,    -1,    49,    50,    -1,    52,    53,    54,    55,
     156,    57,    -1,    -1,    -1,     4,    -1,     6,     7,     8,
       9,    10,    11,    12,    -1,    -1,    -1,    -1,    -1,   164,
      -1,    20,    21,   168,    -1,   170,    25,    26,    -1,   176,
      -1,    -1,   177,    -1,    -1,    -1,    -1,     5,    37,    -1,
     185,    -1,   171,   190,   173,    13,    14,    15,    16,    17,
      18,    19,    -1,    52,    22,    23,    24,    56,    48,    -1,
      50,    51,    52,    53,    54,    55,    56,    -1,    -1,    -1,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      48,    -1,    50,    51,    52,    53,    54,    55,    56,    -1,
      -1,     4,    60,     6,     7,     8,     9,    10,    11,    12,
      50,    51,    52,    53,    54,    55,    56,    20,    21,    -1,
      -1,    -1,    25,    26,    -1,    -1,    -1,     5,    -1,    -1,
      -1,    -1,    -1,    -1,    37,    13,    14,    15,    16,    17,
      18,    19,    -1,    -1,    22,    23,    24,    -1,    -1,    52,
      -1,    -1,    -1,    56,    -1,    -1,    -1,     5,    -1,    -1,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      48,    -1,    50,    51,    52,    53,    54,    55,    56,    27,
      28,    29,    30,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    41,    42,    43,    -1,    -1,    -1,    -1,
      48,    49,    50,    -1,    52,    53,    54,    55,    13,    14,
      15,    16,    17,    18,    19,    -1,    -1,    22,    23,    24,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,    48,    -1,    50,    51,    52,    53,    54,
      55,    56,    -1,    -1,    59,    13,    14,    15,    16,    17,
      18,    19,    -1,    -1,    22,    23,    24,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      48,    -1,    50,    51,    52,    53,    54,    55,    56,    57,
      13,    14,    15,    16,    17,    18,    19,    -1,    -1,    22,
      23,    24,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    35,    -1,    -1,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,    48,    -1,    50,    51,    52,
      53,    54,    55,    56,    13,    14,    15,    16,    17,    18,
      19,    -1,    -1,    22,    23,    24,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    48,
      -1,    50,    51,    52,    53,    54,    55,    56,    15,    16,
      17,    18,    19,    -1,    -1,    22,    23,    24,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,    48,    -1,    50,    51,    52,    53,    54,    55,    56,
      22,    23,    24,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    22,    23,    24,    -1,    -1,    41,
      42,    43,    44,    45,    46,    -1,    48,    -1,    50,    51,
      52,    53,    54,    55,    56,    43,    44,    45,    46,    -1,
      48,    -1,    50,    51,    52,    53,    54,    55,    56,    27,
      28,    29,    30,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      38,    -1,    -1,    41,    42,    43,    27,    28,    29,    30,
      -1,    49,    50,    -1,    52,    53,    54,    55,    -1,    -1,
      41,    42,    43,    27,    28,    29,    30,    48,    49,    50,
      -1,    52,    53,    54,    55,    -1,    -1,    41,    42,    43,
      -1,    -1,    -1,    -1,    -1,    49,    50,    -1,    52,    53,
      54,    55
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    27,    28,    29,    30,    41,    42,    43,    49,    50,
      52,    53,    54,    55,    62,    63,    67,    68,    69,    72,
      75,    79,    80,    81,    54,    55,    68,    68,    27,    49,
      58,    66,    68,    68,     1,    35,    57,    68,    70,    71,
      29,    38,    63,    68,    69,    76,    78,     0,    35,    13,
      14,    15,    16,    17,    18,    19,    22,    23,    24,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    48,    50,
      51,    52,    53,    54,    55,    56,    65,     4,     6,     7,
       8,     9,    10,    11,    12,    20,    21,    25,    26,    37,
      56,    65,    37,    29,    78,    27,    66,    58,    57,    57,
       5,    60,    35,    36,    57,    35,    57,    29,    69,    59,
      52,     1,     3,    36,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    48,    64,    68,    29,    78,
      29,    63,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    29,    68,    59,    68,    69,    73,    74,    68,
      70,    68,    70,     5,    77,    63,    76,    68,    36,    57,
       5,    37,    59,    37,    57,    40,    35,    36,    57,    57,
      68,    64,    68,    63,    63,    42,    74,    68,    57,    68,
      35,    74
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    61,    62,    63,    63,    63,    63,    64,    64,    64,
      64,    65,    65,    66,    66,    67,    67,    67,    67,    67,
      67,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    68,    68,    68,    68,    69,    69,
      69,    70,    70,    71,    71,    72,    72,    72,    72,    72,
      72,    73,    74,    74,    74,    74,    75,    76,    76,    76,
      77,    76,    78,    78,    79,    80,    81,    81,    81,    81
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     0,     1,     2,     3,     0,     1,     3,
       2,     5,     3,     1,     2,     1,     2,     2,     2,     3,
       3,     1,     1,     1,     3,     1,     2,     1,     4,     1,
       1,     1,     1,     1,     3,     3,     2,     2,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     2,     2,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     2,     2,
       3,     2,     2,     2,     2,     1,     3,     3,     1,     2,
       3,     1,     3,     3,     3,     2,     5,     3,     3,     3,
       3,     4,     1,     3,     3,     5,     5,     1,     4,     2,
       0,     4,     1,     3,     4,     3,     6,     5,     3,     4
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
      yyerror (&yylloc, lex, YY_("syntax error: cannot back up")); \
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
#if YYDEBUG

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
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

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
                  Type, Value, Location, lex); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, char **lex)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (yylocationp);
  YYUSE (lex);
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
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, char **lex)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, lex);
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
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, char **lex)
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
                       , &(yylsp[(yyi + 1) - (yynrhs)])                       , lex);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, lex); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


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
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, char **lex)
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (lex);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  switch (yytype)
    {
          case 63: /* seq  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1322 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 64: /* range  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1328 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 65: /* matrix_index  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1334 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 66: /* backticks  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1340 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 67: /* history  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1346 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 68: /* expr  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1352 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 69: /* lvalue  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1358 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 70: /* matrixelts  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1364 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 71: /* matrixlines  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1370 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 72: /* matrix  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1376 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 73: /* in  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1382 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 74: /* inseq  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1388 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 75: /* compr  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1394 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 76: /* arg  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1400 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 78: /* listarg  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1406 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 79: /* funcid  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1412 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 80: /* memberid  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1418 "../src/language/parse.c" /* yacc.c:1257  */
        break;

    case 81: /* definition  */
#line 83 "../src/language/parse.y" /* yacc.c:1257  */
      { pari_discarded++; }
#line 1424 "../src/language/parse.c" /* yacc.c:1257  */
        break;


      default:
        break;
    }
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/*----------.
| yyparse.  |
`----------*/

int
yyparse (char **lex)
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
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
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

/* User initialization code.  */
#line 30 "../src/language/parse.y" /* yacc.c:1429  */
{ yylloc.start=yylloc.end=*lex; }

#line 1535 "../src/language/parse.c" /* yacc.c:1429  */
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
      yychar = yylex (&yylval, &yylloc, lex);
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
#line 86 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1724 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 3:
#line 89 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=NOARG((yyloc));}
#line 1730 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 4:
#line 90 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1736 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 5:
#line 91 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[-1].val); (yyloc)=(yylsp[-1]);}
#line 1742 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 6:
#line 92 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fseq,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1748 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 7:
#line 95 "../src/language/parse.y" /* yacc.c:1646  */
    { (yyval.val)=newnode(Frange,NORANGE((yyloc)),NORANGE((yyloc)),&(yyloc)); }
#line 1754 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 8:
#line 96 "../src/language/parse.y" /* yacc.c:1646  */
    { (yyval.val)=newnode(Frange,(yyvsp[0].val),NORANGE((yyloc)),&(yyloc)); }
#line 1760 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 9:
#line 97 "../src/language/parse.y" /* yacc.c:1646  */
    { (yyval.val)=newnode(Frange,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc)); }
#line 1766 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 10:
#line 98 "../src/language/parse.y" /* yacc.c:1646  */
    { (yyval.val)=newnode(Frange,NORANGE((yyloc)),(yyvsp[0].val),&(yyloc)); }
#line 1772 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 11:
#line 101 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatrix,(yyvsp[-3].val),(yyvsp[-1].val),&(yyloc));}
#line 1778 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 12:
#line 102 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatrix,(yyvsp[-1].val),-1,&(yyloc));}
#line 1784 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 13:
#line 105 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=1;}
#line 1790 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 14:
#line 106 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[-1].val)+1;}
#line 1796 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 15:
#line 109 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPhist,-1,-1,&(yyloc));}
#line 1802 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 16:
#line 110 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPhist,newintnode(&(yylsp[0])),-1,&(yyloc));}
#line 1808 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 17:
#line 111 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPhist,newnode(Fsmall,-(yyvsp[0].val),-1,&(yyloc)),-1,&(yyloc));}
#line 1814 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 18:
#line 112 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPhisttime,-1,-1,&(yyloc));}
#line 1820 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 19:
#line 113 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPhisttime,newintnode(&(yylsp[0])),-1,&(yyloc));}
#line 1826 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 20:
#line 114 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPhisttime,newnode(Fsmall,-(yyvsp[0].val),-1,&(yyloc)),-1,&(yyloc));}
#line 1832 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 21:
#line 117 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newintnode(&(yylsp[0]));}
#line 1838 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 22:
#line 118 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newconst(CSTreal,&(yyloc));}
#line 1844 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 23:
#line 119 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newconst(CSTreal,&(yyloc));}
#line 1850 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 24:
#line 120 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Ffunction,newconst(CSTmember,&(yylsp[0])),
                                                newintnode(&(yylsp[-2])),&(yyloc));}
#line 1857 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 25:
#line 122 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newconst(CSTstr,&(yyloc));}
#line 1863 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 26:
#line 123 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newconst(CSTquote,&(yyloc));}
#line 1869 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 27:
#line 124 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1875 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 28:
#line 125 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fcall,(yyvsp[-3].val),(yyvsp[-1].val),&(yyloc));}
#line 1881 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 29:
#line 126 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1887 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 30:
#line 127 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1893 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 31:
#line 128 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1899 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 32:
#line 129 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1905 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 33:
#line 130 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 1911 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 34:
#line 131 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fassign,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1917 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 35:
#line 132 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fassign,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1923 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 36:
#line 133 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPpp,(yyvsp[-1].val),-1,&(yyloc));}
#line 1929 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 37:
#line 134 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPss,(yyvsp[-1].val),-1,&(yyloc));}
#line 1935 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 38:
#line 135 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPme,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1941 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 39:
#line 136 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPde,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1947 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 40:
#line 137 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPdre,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1953 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 41:
#line 138 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPeuce,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1959 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 42:
#line 139 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPmode,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1965 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 43:
#line 140 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPsle,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1971 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 44:
#line 141 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPsre,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1977 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 45:
#line 142 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPpe,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1983 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 46:
#line 143 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPse,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 1989 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 47:
#line 144 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPnb,(yyvsp[0].val),-1,&(yyloc));}
#line 1995 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 48:
#line 145 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPlength,(yyvsp[0].val),-1,&(yyloc));}
#line 2001 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 49:
#line 146 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPor,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2007 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 50:
#line 147 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPand,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2013 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 51:
#line 148 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPand,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2019 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 52:
#line 149 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPid,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2025 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 53:
#line 150 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPeq,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2031 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 54:
#line 151 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPne,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2037 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 55:
#line 152 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPge,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2043 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 56:
#line 153 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPg,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2049 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 57:
#line 154 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPle,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2055 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 58:
#line 155 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPl,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2061 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 59:
#line 156 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPs,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2067 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 60:
#line 157 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPp,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2073 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 61:
#line 158 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPsl,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2079 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 62:
#line 159 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPsr,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2085 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 63:
#line 160 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPmod,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2091 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 64:
#line 161 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPdr,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2097 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 65:
#line 162 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPeuc,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2103 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 66:
#line 163 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPd,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2109 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 67:
#line 164 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPm,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2115 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 68:
#line 165 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 2121 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 69:
#line 166 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPn,(yyvsp[0].val),-1,&(yyloc));}
#line 2127 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 70:
#line 167 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPpow,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2133 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 71:
#line 168 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPtrans,(yyvsp[-1].val),-1,&(yyloc));}
#line 2139 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 72:
#line 169 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPderiv,(yyvsp[-1].val),-1,&(yyloc));}
#line 2145 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 73:
#line 170 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPfact,(yyvsp[-1].val),-1,&(yyloc));}
#line 2151 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 74:
#line 171 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatcoeff,(yyvsp[-1].val),(yyvsp[0].val),&(yyloc));}
#line 2157 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 75:
#line 172 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 2163 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 76:
#line 173 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Ftag,(yyvsp[-2].val),0,&(yyloc));}
#line 2169 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 77:
#line 174 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[-1].val);}
#line 2175 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 78:
#line 177 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fentry,newconst(CSTentry,&(yylsp[0])),-1,&(yyloc));}
#line 2181 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 79:
#line 178 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatcoeff,(yyvsp[-1].val),(yyvsp[0].val),&(yyloc));}
#line 2187 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 80:
#line 179 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Ftag,(yyvsp[-2].val),newconst(CSTentry,&(yylsp[-1])),&(yyloc));}
#line 2193 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 81:
#line 182 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 2199 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 82:
#line 183 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatrixelts,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2205 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 83:
#line 186 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatrixlines,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2211 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 84:
#line 187 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmatrixlines,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2217 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 85:
#line 190 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fvec,-1,-1,&(yyloc));}
#line 2223 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 86:
#line 191 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPrange,(yyvsp[-3].val),(yyvsp[-1].val),&(yyloc));}
#line 2229 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 87:
#line 192 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmat,-1,-1,&(yyloc));}
#line 2235 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 88:
#line 193 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fvec,(yyvsp[-1].val),-1,&(yyloc));}
#line 2241 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 89:
#line 194 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fmat,(yyvsp[-1].val),-1,&(yyloc));}
#line 2247 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 90:
#line 195 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=-1; YYABORT;}
#line 2253 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 91:
#line 198 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Flistarg,(yyvsp[0].val),(yyvsp[-3].val),&(yyloc));}
#line 2259 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 92:
#line 201 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPcompr,(yyvsp[0].val),-2,&(yyloc));}
#line 2265 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 93:
#line 202 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall3(OPcompr,(yyvsp[-2].val),-2,(yyvsp[0].val),&(yyloc));}
#line 2271 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 94:
#line 203 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall(OPcomprc,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2277 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 95:
#line 204 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newopcall3(OPcomprc,(yyvsp[-4].val),(yyvsp[0].val),(yyvsp[-2].val),&(yyloc));}
#line 2283 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 96:
#line 207 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=addcurrexpr((yyvsp[-1].val),(yyvsp[-3].val),&(yyloc));}
#line 2289 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 97:
#line 210 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 2295 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 98:
#line 211 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Fvararg,(yyvsp[-3].val),-1,&(yyloc));}
#line 2301 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 99:
#line 212 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Frefarg,(yyvsp[0].val),-1,&(yyloc));}
#line 2307 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 100:
#line 213 "../src/language/parse.y" /* yacc.c:1646  */
    {if (!pari_once) { yyerrok; } pari_once=1;}
#line 2313 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 101:
#line 214 "../src/language/parse.y" /* yacc.c:1646  */
    {pari_once=0; (yyval.val)=newopcall(OPcat,(yyvsp[-3].val),(yyvsp[0].val),&(yyloc));}
#line 2319 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 102:
#line 217 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=(yyvsp[0].val);}
#line 2325 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 103:
#line 218 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Flistarg,(yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2331 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 104:
#line 221 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Ffunction,newconst(CSTentry,&(yylsp[-3])),(yyvsp[-1].val),&(yyloc));}
#line 2337 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 105:
#line 224 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Ffunction,newconst(CSTmember,&(yylsp[0])),(yyvsp[-2].val),&(yyloc));}
#line 2343 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 106:
#line 228 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newfunc(CSTentry,&(yylsp[-5]),(yyvsp[-3].val),(yyvsp[0].val),&(yyloc));}
#line 2349 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 107:
#line 230 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newfunc(CSTmember,&(yylsp[-2]),(yyvsp[-4].val),(yyvsp[0].val),&(yyloc));}
#line 2355 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 108:
#line 231 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Flambda, (yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2361 "../src/language/parse.c" /* yacc.c:1646  */
    break;

  case 109:
#line 232 "../src/language/parse.y" /* yacc.c:1646  */
    {(yyval.val)=newnode(Flambda, (yyvsp[-2].val),(yyvsp[0].val),&(yyloc));}
#line 2367 "../src/language/parse.c" /* yacc.c:1646  */
    break;


#line 2371 "../src/language/parse.c" /* yacc.c:1646  */
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
      yyerror (&yylloc, lex, YY_("syntax error"));
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
        yyerror (&yylloc, lex, yymsgp);
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
                      yytoken, &yylval, &yylloc, lex);
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
                  yystos[yystate], yyvsp, yylsp, lex);
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
  yyerror (&yylloc, lex, YY_("memory exhausted"));
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
                  yytoken, &yylval, &yylloc, lex);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp, yylsp, lex);
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
#line 235 "../src/language/parse.y" /* yacc.c:1906  */

