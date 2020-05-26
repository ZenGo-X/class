#line 2 "../src/kernel/none/gcdext.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*==================================
 * bezout(a,b,pu,pv)
 *==================================
 *    Return g = gcd(a,b) >= 0, and assign GENs u,v through pointers pu,pv
 *    such that g = u*a + v*b.
 * Special cases:
 *    a == b == 0 ==> pick u=1, v=0
 *    a != 0 == b ==> keep v=0
 *    a == 0 != b ==> keep u=0
 *    |a| == |b| != 0 ==> keep u=0, set v=+-1
 * Assignments through pu,pv will be suppressed when the corresponding
 * pointer is NULL  (but the computations will happen nonetheless).
 */

GEN
bezout(GEN a, GEN b, GEN *pu, GEN *pv)
{
  GEN t,u,u1,v,v1,d,d1,q,r;
  GEN *pt;
  pari_sp av, av1;
  long s, sa, sb;
  ulong g;
  ulong xu,xu1,xv,xv1;                /* Lehmer stage recurrence matrix */
  int lhmres;                        /* Lehmer stage return value */

  s = abscmpii(a,b);
  if (s < 0)
  {
    t=b; b=a; a=t;
    pt=pu; pu=pv; pv=pt;
  }
  /* now |a| >= |b| */

  sa = signe(a); sb = signe(b);
  if (!sb)
  {
    if (pv) *pv = gen_0;
    switch(sa)
    {
    case  0: if (pu) *pu = gen_0; return gen_0;
    case  1: if (pu) *pu = gen_1; return icopy(a);
    case -1: if (pu) *pu = gen_m1; return(negi(a));
    }
  }
  if (s == 0)                        /* |a| == |b| != 0 */
  {
    if (pu) *pu = gen_0;
    if (sb > 0)
    { if (pv) *pv = gen_1; return icopy(b); }
    else
    { if (pv) *pv = gen_m1; return(negi(b)); }
  }
  /* now |a| > |b| > 0 */

  if (lgefint(a) == 3)                /* single-word affair */
  {
    g = xxgcduu(uel(a,2), uel(b,2), 0, &xu, &xu1, &xv, &xv1, &s);
    sa = s > 0 ? sa : -sa;
    sb = s > 0 ? -sb : sb;
    if (pu)
    {
      if (xu == 0) *pu = gen_0; /* can happen when b divides a */
      else if (xu == 1) *pu = sa < 0 ? gen_m1 : gen_1;
      else if (xu == 2) *pu = sa < 0 ? gen_m2 : gen_2;
      else
      {
        *pu = cgeti(3);
        (*pu)[1] = evalsigne(sa)|evallgefint(3);
        (*pu)[2] = xu;
      }
    }
    if (pv)
    {
      if (xv == 1) *pv = sb < 0 ? gen_m1 : gen_1;
      else if (xv == 2) *pv = sb < 0 ? gen_m2 : gen_2;
      else
      {
        *pv = cgeti(3);
        (*pv)[1] = evalsigne(sb)|evallgefint(3);
        (*pv)[2] = xv;
      }
    }
    if      (g == 1) return gen_1;
    else if (g == 2) return gen_2;
    else return utoipos(g);
  }

  /* general case */
  av = avma;
  (void)new_chunk(lgefint(b) + (lgefint(a)<<1)); /* room for u,v,gcd */
  /* if a is significantly larger than b, calling lgcdii() is not the best
   * way to start -- reduce a mod b first
   */
  if (lgefint(a) > lgefint(b))
  {
    d = absi_shallow(b);
    q = dvmdii(absi_shallow(a), d, &d1);
    if (!signe(d1))                /* a == qb */
    {
      avma = av;
      if (pu) *pu = gen_0;
      if (pv) *pv = sb < 0 ? gen_m1 : gen_1;
      return icopy(d);
    }
    else
    {
      u = gen_0;
      u1 = v = gen_1;
      v1 = negi(q);
    }
    /* if this results in lgefint(d) == 3, will fall past main loop */
  }
  else
  {
    d = absi_shallow(a);
    d1 = absi_shallow(b);
    u = v1 = gen_1; u1 = v = gen_0;
  }
  av1 = avma;

  /* main loop is almost identical to that of invmod() */
  while (lgefint(d) > 3 && signe(d1))
  {
    lhmres = lgcdii((ulong *)d, (ulong *)d1, &xu, &xu1, &xv, &xv1, ULONG_MAX);
    if (lhmres != 0)                /* check progress */
    {                                /* apply matrix */
      if ((lhmres == 1) || (lhmres == -1))
      {
        if (xv1 == 1)
        {
          r = subii(d,d1); d=d1; d1=r;
          a = subii(u,u1); u=u1; u1=a;
          a = subii(v,v1); v=v1; v1=a;
        }
        else
        {
          r = subii(d, mului(xv1,d1)); d=d1; d1=r;
          a = subii(u, mului(xv1,u1)); u=u1; u1=a;
          a = subii(v, mului(xv1,v1)); v=v1; v1=a;
        }
      }
      else
      {
        r  = subii(muliu(d,xu),  muliu(d1,xv));
        d1 = subii(muliu(d,xu1), muliu(d1,xv1)); d = r;
        a  = subii(muliu(u,xu),  muliu(u1,xv));
        u1 = subii(muliu(u,xu1), muliu(u1,xv1)); u = a;
        a  = subii(muliu(v,xu),  muliu(v1,xv));
        v1 = subii(muliu(v,xu1), muliu(v1,xv1)); v = a;
        if (lhmres&1) { togglesign(d);  togglesign(u);  togglesign(v); }
        else          { togglesign(d1); togglesign(u1); togglesign(v1); }
      }
    }
    if (lhmres <= 0 && signe(d1))
    {
      q = dvmdii(d,d1,&r);
      a = subii(u,mulii(q,u1));
      u=u1; u1=a;
      a = subii(v,mulii(q,v1));
      v=v1; v1=a;
      d=d1; d1=r;
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"bezout");
      gerepileall(av1,6, &d,&d1,&u,&u1,&v,&v1);
    }
  } /* end while */

  /* Postprocessing - final sprint */
  if (signe(d1))
  {
    /* Assertions: lgefint(d)==lgefint(d1)==3, and
     * gcd(d,d1) is nonzero and fits into one word
     */
    g = xxgcduu(uel(d,2), uel(d1,2), 0, &xu, &xu1, &xv, &xv1, &s);
    u = subii(muliu(u,xu), muliu(u1, xv));
    v = subii(muliu(v,xu), muliu(v1, xv));
    if (s < 0) { sa = -sa; sb = -sb; }
    avma = av;
    if (pu) *pu = sa < 0 ? negi(u) : icopy(u);
    if (pv) *pv = sb < 0 ? negi(v) : icopy(v);
    if (g == 1) return gen_1;
    else if (g == 2) return gen_2;
    else return utoipos(g);
  }
  /* get here when the final sprint was skipped (d1 was zero already).
   * Now the matrix is final, and d contains the gcd.
   */
  avma = av;
  if (pu) *pu = sa < 0 ? negi(u) : icopy(u);
  if (pv) *pv = sb < 0 ? negi(v) : icopy(v);
  return icopy(d);
}

