/* Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

BEGINEXTERN

typedef enum {Fseq,
              Fmatrix,Frange,
              Fassign,
              Fmatcoeff,
              Fmatrixelts,Fmatrixlines,
              Fmat,Fvec,Fnoarg,Fnorange,
              Flistarg,
              Frefarg, Fvararg,
              Fconst,Fsmall,
              Ftag,
              Fentry,Fcall,Ffunction,Flambda
} Ffunc;

#define Flastfunc  (Fdeffunc)
#define FneedENTRY (Fconst)

typedef struct node_s
{
  Ffunc f;           /*node function   */
  long x;            /*node left child */
  long y;            /*node right child*/
  const char *str;   /*text start      */
  size_t len;        /*text length     */
  long flags;        /*flags from the copy optimizer*/
} node;

typedef enum {CSTstr, CSTquote, CSTint, CSTreal, CSTmember, CSTentry} CSTtype;

typedef enum {OPor, OPand, OPid, OPeq, OPne, OPge, OPg, OPle, OPl, OPs, OPp, OPsl, OPsr, OPmod, OPdr, OPeuc, OPd, OPm, OPpow, OPcat, OPss, OPpp, OPse ,OPpe ,OPsle ,OPsre ,OPmode ,OPdre ,OPeuce ,OPde ,OPme, OPpl, OPn, OPnb, OPfact, OPderiv, OPtrans, OPrange, OPcompr, OPcomprc, OPhist, OPhisttime, OPlength, OPnboperator} OPerator;

extern THREAD node *pari_tree;

ENDEXTERN
