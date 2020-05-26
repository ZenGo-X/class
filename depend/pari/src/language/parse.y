%{
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
%}
%error-verbose
%name-prefix "pari_"
%pure-parser
%parse-param {char **lex}
%lex-param {char **lex}
%initial-action{ @$.start=@$.end=*lex; }
%token KPARROW ")->"
%token KARROW "->"
%token KDOTDOT ".."
%token KPE   "+="
%token KSE   "-="
%token KME   "*="
%token KDE   "/="
%token KDRE  "\\/="
%token KEUCE "\\="
%token KMODE "%="
%token KAND  "&&"
%token KOR   "||"
%token KID   "==="
%token KEQ   "=="
%token KNE   "!="
%token KGE   ">="
%token KLE   "<="
%token KSRE  ">>="
%token KSLE  "<<="
%token KSR   ">>"
%token KSL   "<<"
%token KDR   "\\/"
%token KPP   "++"
%token KSS   "--"
%token <gen> KINTEGER "integer"
%token <gen> KREAL "real number"
%token KENTRY "variable name"
%token KSTRING "character string"
%left SEQ DEFFUNC
%left INT LVAL
%right ")->" "->"
%left ';' ',' ".."
%right '=' "+=" "-=" "*=" "/=" "\\/=" "\\=" "%=" ">>=" "<<="
%left '&' "&&" "||"
%left "===" "==" "!=" '>' ">=" '<' "<="
%left '+' '-'
%left '%' "\\/" '\\' '/' '*' ">>" "<<"
%left SIGN
%right '^'
%left '#'
%left '!' '~' '[' '\''
%left '.'
%left "++" "--"
%left '('
%left ':'
%type <val> seq sequence
%type <val> range matrix matrix_index expr
%type <val> lvalue
%type <val> matrixelts matrixlines arg listarg definition
%type <val> funcid memberid
%type <val> backticks history
%type <val> compr in inseq
%destructor { pari_discarded++; } seq matrix range matrix_index expr lvalue matrixelts matrixlines arg listarg definition funcid memberid backticks history compr in inseq
%%

sequence: seq        {$$=$1;} /* skip the destructor */
;

seq: /**/ %prec SEQ  {$$=NOARG(@$);}
   | expr %prec SEQ  {$$=$1;}
   | seq ';'         {$$=$1; @$=@1;}
   | seq ';' expr    {$$=newnode(Fseq,$1,$3,&@$);}
;

range: /* */          { $$=newnode(Frange,NORANGE(@$),NORANGE(@$),&@$); }
     | expr           { $$=newnode(Frange,$1,NORANGE(@$),&@$); }
     | expr ".." expr { $$=newnode(Frange,$1,$3,&@$); }
     | '^' expr       { $$=newnode(Frange,NORANGE(@$),$2,&@$); }
;

matrix_index: '[' range ',' range ']' {$$=newnode(Fmatrix,$2,$4,&@$);}
            | '[' range ']'           {$$=newnode(Fmatrix,$2,-1,&@$);}
;

backticks: '`' {$$=1;}
         | backticks '`' {$$=$1+1;}
;

history: '%'           {$$=newopcall(OPhist,-1,-1,&@$);}
       | '%' KINTEGER  {$$=newopcall(OPhist,newintnode(&@2),-1,&@$);}
       | '%' backticks {$$=newopcall(OPhist,newnode(Fsmall,-$2,-1,&@$),-1,&@$);}
       | '%' '#'          {$$=newopcall(OPhisttime,-1,-1,&@$);}
       | '%' '#' KINTEGER {$$=newopcall(OPhisttime,newintnode(&@3),-1,&@$);}
       | '%' '#' backticks{$$=newopcall(OPhisttime,newnode(Fsmall,-$3,-1,&@$),-1,&@$);}
;

expr: KINTEGER %prec INT  {$$=newintnode(&@1);}
    | KREAL               {$$=newconst(CSTreal,&@$);}
    | '.'                 {$$=newconst(CSTreal,&@$);}
    | KINTEGER '.' KENTRY {$$=newnode(Ffunction,newconst(CSTmember,&@3),
                                                newintnode(&@1),&@$);}
    | KSTRING       {$$=newconst(CSTstr,&@$);}
    | '\'' KENTRY   {$$=newconst(CSTquote,&@$);}
    | history           {$$=$1;}
    | expr '(' listarg ')'  {$$=newnode(Fcall,$1,$3,&@$);}
    | funcid            {$$=$1;}
    | lvalue %prec LVAL {$$=$1;}
    | matrix            {$$=$1;}
    | compr             {$$=$1;}
    | definition        {$$=$1;}
    | matrix '=' expr {$$=newnode(Fassign,$1,$3,&@$);}
    | lvalue '=' expr {$$=newnode(Fassign,$1,$3,&@$);}
    | lvalue "++"     {$$=newopcall(OPpp,$1,-1,&@$);}
    | lvalue "--"     {$$=newopcall(OPss,$1,-1,&@$);}
    | lvalue "*="   expr {$$=newopcall(OPme,$1,$3,&@$);}
    | lvalue "/="   expr {$$=newopcall(OPde,$1,$3,&@$);}
    | lvalue "\\/=" expr {$$=newopcall(OPdre,$1,$3,&@$);}
    | lvalue "\\="  expr {$$=newopcall(OPeuce,$1,$3,&@$);}
    | lvalue "%="   expr {$$=newopcall(OPmode,$1,$3,&@$);}
    | lvalue "<<="  expr {$$=newopcall(OPsle,$1,$3,&@$);}
    | lvalue ">>="  expr {$$=newopcall(OPsre,$1,$3,&@$);}
    | lvalue "+="   expr {$$=newopcall(OPpe,$1,$3,&@$);}
    | lvalue "-="   expr {$$=newopcall(OPse,$1,$3,&@$);}
    | '!' expr         {$$=newopcall(OPnb,$2,-1,&@$);}
    | '#' expr         {$$=newopcall(OPlength,$2,-1,&@$);}
    | expr "||"  expr  {$$=newopcall(OPor,$1,$3,&@$);}
    | expr "&&"  expr  {$$=newopcall(OPand,$1,$3,&@$);}
    | expr '&'   expr  {$$=newopcall(OPand,$1,$3,&@$);}
    | expr "===" expr  {$$=newopcall(OPid,$1,$3,&@$);}
    | expr "=="  expr  {$$=newopcall(OPeq,$1,$3,&@$);}
    | expr "!="  expr  {$$=newopcall(OPne,$1,$3,&@$);}
    | expr ">="  expr  {$$=newopcall(OPge,$1,$3,&@$);}
    | expr '>'   expr  {$$=newopcall(OPg,$1,$3,&@$);}
    | expr "<="  expr  {$$=newopcall(OPle,$1,$3,&@$);}
    | expr '<'   expr  {$$=newopcall(OPl,$1,$3,&@$);}
    | expr '-'   expr  {$$=newopcall(OPs,$1,$3,&@$);}
    | expr '+'   expr  {$$=newopcall(OPp,$1,$3,&@$);}
    | expr "<<"  expr  {$$=newopcall(OPsl,$1,$3,&@$);}
    | expr ">>"  expr  {$$=newopcall(OPsr,$1,$3,&@$);}
    | expr '%'   expr  {$$=newopcall(OPmod,$1,$3,&@$);}
    | expr "\\/" expr  {$$=newopcall(OPdr,$1,$3,&@$);}
    | expr '\\'  expr  {$$=newopcall(OPeuc,$1,$3,&@$);}
    | expr '/'   expr  {$$=newopcall(OPd,$1,$3,&@$);}
    | expr '*'   expr  {$$=newopcall(OPm,$1,$3,&@$);}
    | '+' expr %prec SIGN {$$=$2;}
    | '-' expr %prec SIGN {$$=newopcall(OPn,$2,-1,&@$);}
    | expr '^' expr {$$=newopcall(OPpow,$1,$3,&@$);}
    | expr '~' {$$=newopcall(OPtrans,$1,-1,&@$);}
    | expr '\'' {$$=newopcall(OPderiv,$1,-1,&@$);}
    | expr '!'  {$$=newopcall(OPfact,$1,-1,&@$);}
    | expr matrix_index {$$=newnode(Fmatcoeff,$1,$2,&@$);}
    | memberid {$$=$1;}
    | expr ':' KENTRY   {$$=newnode(Ftag,$1,0,&@$);}
    | '(' expr ')' {$$=$2;}
;

lvalue: KENTRY %prec LVAL   {$$=newnode(Fentry,newconst(CSTentry,&@1),-1,&@$);}
      | lvalue matrix_index {$$=newnode(Fmatcoeff,$1,$2,&@$);}
      | lvalue ':' KENTRY   {$$=newnode(Ftag,$1,newconst(CSTentry,&@2),&@$);}
;

matrixelts: expr {$$=$1;}
          | matrixelts ',' expr {$$=newnode(Fmatrixelts,$1,$3,&@$);}
;

matrixlines: matrixelts  ';' matrixelts {$$=newnode(Fmatrixlines,$1,$3,&@$);}
           | matrixlines ';' matrixelts {$$=newnode(Fmatrixlines,$1,$3,&@$);}
;

matrix: '[' ']'             {$$=newnode(Fvec,-1,-1,&@$);}
      | '[' expr ".." expr ']' {$$=newopcall(OPrange,$2,$4,&@$);}
      | '[' ';' ']'         {$$=newnode(Fmat,-1,-1,&@$);}
      | '[' matrixelts ']'  {$$=newnode(Fvec,$2,-1,&@$);}
      | '[' matrixlines ']' {$$=newnode(Fmat,$2,-1,&@$);}
      | '[' error ']'       {$$=-1; YYABORT;}
;

in: lvalue '<' '-' expr {$$=newnode(Flistarg,$4,$1,&@$);}
;

inseq: in                    {$$=newopcall(OPcompr,$1,-2,&@$);}
     | in ',' expr           {$$=newopcall3(OPcompr,$1,-2,$3,&@$);}
     | in ';' inseq          {$$=newopcall(OPcomprc,$1,$3,&@$);}
     | in ',' expr ';' inseq {$$=newopcall3(OPcomprc,$1,$5,$3,&@$);}
;

compr: '[' expr '|' inseq ']' {$$=addcurrexpr($4,$2,&@$);}
;

arg: seq        {$$=$1;}
   | lvalue '[' ".." ']' {$$=newnode(Fvararg,$1,-1,&@$);}
   | '&' lvalue {$$=newnode(Frefarg,$2,-1,&@$);}
   | arg error  {if (!pari_once) { yyerrok; } pari_once=1;}  expr
                     {pari_once=0; $$=newopcall(OPcat,$1,$4,&@$);}
;

listarg: arg {$$=$1;}
       | listarg ',' arg {$$=newnode(Flistarg,$1,$3,&@$);}
;

funcid: KENTRY '(' listarg ')' {$$=newnode(Ffunction,newconst(CSTentry,&@1),$3,&@$);}
;

memberid: expr '.' KENTRY {$$=newnode(Ffunction,newconst(CSTmember,&@3),$1,&@$);}
;

definition: KENTRY '(' listarg ')' '=' seq %prec DEFFUNC
                                   {$$=newfunc(CSTentry,&@1,$3,$6,&@$);}
          | expr '.' KENTRY '=' seq %prec DEFFUNC
                                   {$$=newfunc(CSTmember,&@3,$1,$5,&@$);}
          | lvalue "->" seq              {$$=newnode(Flambda, $1,$3,&@$);}
          | '(' listarg ")->" seq        {$$=newnode(Flambda, $2,$4,&@$);}
;

%%
