/* Copyright (C) 2017  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* for loop over permutations in lexicographic order
 * This implements the algorithm L in D. Knuth "The Art Of Computer Programming"
 * Fascicle 2b */

#include "pari.h"
#include "paripriv.h"

void
forperm_init(forperm_t *T, GEN k)
{
  switch (typ(k))
  {
    case t_INT:
      if (signe(k) < 0) pari_err_DOMAIN("forperm", "a", "<", gen_0, k);
      T->v = identity_perm(itou(k)); break;
    case t_VEC:
      T->v = vec_to_vecsmall(k); break;
    case t_VECSMALL:
      T->v = vecsmall_copy(k); break;
    default:
      pari_err_TYPE("forperm", k);
      return; /* LCOV_EXCL_LINE */
  }
  T->first = 1;
  T->k = lg(T->v) - 1;
}

GEN
forperm_next(forperm_t *T)
{
  long k = T->k, m1, m2, *p, *q;
  GEN v = T->v;

  if (T->first) { T->first = 0; return v; }
  m1 = k-1; while (m1 > 0 && v[m1] >= v[m1+1]) m1--;
  if (m1 <= 0) return NULL;

  m2 = k; while (v[m1] >= v[m2]) m2--;
  lswap(v[m1], v[m2]);
  p = v + m1 + 1;
  q = v + k;
  while (p < q) { lswap(*p, *q); p++; q--; }
  return v;
}

void
forperm(void *E, long call(void *, GEN), GEN k)
{
  pari_sp av = avma;
  forperm_t T;
  GEN v;

  forperm_init(&T, k);
  while ((v = forperm_next(&T)))
    if (call(E, v)) break;
  avma = av;
}

void
forperm0(GEN k, GEN code)
{
  push_lex(gen_0, code);
  forperm((void *)code, &gp_evalvoid, k);
  pop_lex(1);
}

