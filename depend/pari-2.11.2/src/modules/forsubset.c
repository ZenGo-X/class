/* Copyright (C) 2017  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

void
forksubset_init(forsubset_t *T, long n, long k)
{
  T->all = 0;
  T->first = 1;
  T->n = n;
  T->k = k;
  T->v = identity_perm(k);
}

void
forallsubset_init(forsubset_t *T, long n)
{
  T->all = 1;
  T->first = 1;
  T->n = n;
  T->k = 0;
  T->v = vecsmalltrunc_init(n + 1);
}

static GEN
forksubset_next(forsubset_t *T)
{
  GEN v = T->v;
  long i, n = T->n, k = T->k;

  if (T->first) { T->first = 0; return (k >= 0 && k <= n) ? v: NULL; }
  if (k <= 0 || k >= n) return NULL;

  if (v[k] < n) { v[k]++; return v; }
  for (i = k - 1; i >= 1 && v[i+1] == v[i] + 1; i--);
  if (i == 0) return NULL;

  v[i]++;
  for (; i < k; i++) v[i+1] = v[i] + 1;
  return v;
}
static GEN
forallsubset_next(forsubset_t *T)
{
  long i;

  if (forksubset_next(T)) return T->v;
  else if (T->k < T->n)
  {
    (T->k)++;
    setlg(T->v, T->k+1);
    for (i = 1; i <= T->k; i++) (T->v)[i] = i;
    return T->v;
  }
  return NULL;
}
GEN
forsubset_next(forsubset_t *T)
{ return T->all? forallsubset_next(T): forksubset_next(T); }
void
forsubset_init(forsubset_t *T, GEN nk)
{
  switch(typ(nk))
  {
    case t_INT: forallsubset_init(T, itos(nk)); return;
    case t_VEC:
      if (lg(nk) == 3)
      {
        GEN n = gel(nk,1), k = gel(nk,2);
        if (typ(n) == t_INT && typ(k) == t_INT)
          return forksubset_init(T, itos(n),itos(k));
      }
    default:
      pari_err_TYPE("forsubset", nk);
  }
}
void
forsubset0(GEN nk, GEN code)
{
  pari_sp av = avma;
  forsubset_t T;
  void *E = (void*)code;
  GEN v;
  push_lex(gen_0, code);
  forsubset_init(&T, nk);
  while ((v = forsubset_next(&T)))
    if (gp_evalvoid(E, v)) break;
  pop_lex(1); avma = av;
}
