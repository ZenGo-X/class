/* Copyright (C) 2006  The PARI group.

This file is part of the PARI package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"
#include "anal.h"
#include "opcode.h"

/********************************************************************/
/*                                                                  */
/*                   break/next/return handling                     */
/*                                                                  */
/********************************************************************/

static THREAD long br_status, br_count;
static THREAD GEN br_res;

long
loop_break(void)
{
  switch(br_status)
  {
    case br_MULTINEXT :
      if (! --br_count) br_status = br_NEXT;
      return 1;
    case br_BREAK : if (! --br_count) br_status = br_NONE; /* fall through */
    case br_RETURN: return 1;
    case br_NEXT: br_status = br_NONE; /* fall through */
  }
  return 0;
}

static void
reset_break(void)
{
  br_status = br_NONE;
  if (br_res) { gunclone_deep(br_res); br_res = NULL; }
}

GEN
return0(GEN x)
{
  GEN y = br_res;
  br_res = (x && x != gnil)? gcloneref(x): NULL;
  if (y) gunclone_deep(y);
  br_status = br_RETURN; return NULL;
}

GEN
next0(long n)
{
  if (n < 1) pari_err_DOMAIN("next", "n", "<", gen_1, stoi(n));
  if (n == 1) br_status = br_NEXT;
  else
  {
    br_count = n-1;
    br_status = br_MULTINEXT;
  }
  return NULL;
}

GEN
break0(long n)
{
  if (n < 1) pari_err_DOMAIN("break", "n", "<", gen_1, stoi(n));
  br_count = n;
  br_status = br_BREAK; return NULL;
}

/*******************************************************************/
/*                                                                 */
/*                            VARIABLES                            */
/*                                                                 */
/*******************************************************************/

/* As a rule, ep->value is a clone (COPY). push_val and pop_val are private
 * functions for use in sumiter: we want a temporary ep->value, which is NOT
 * a clone (PUSH), to avoid unnecessary copies. */

enum {PUSH_VAL = 0, COPY_VAL = 1, DEFAULT_VAL = 2};

/* ep->args is the stack of old values (INITIAL if initial value, from
 * installep) */
typedef struct var_cell {
  struct var_cell *prev; /* cell attached to previous value on stack */
  GEN value; /* last value (not including current one, in ep->value) */
  char flag; /* status of _current_ ep->value: PUSH or COPY ? */
  long valence; /* valence of entree* attached to 'value', to be restored
                    * by pop_val */
} var_cell;
#define INITIAL NULL

/* Push x on value stack attached to ep. */
static void
new_val_cell(entree *ep, GEN x, char flag)
{
  var_cell *v = (var_cell*) pari_malloc(sizeof(var_cell));
  v->value  = (GEN)ep->value;
  v->prev   = (var_cell*) ep->pvalue;
  v->flag   = flag;
  v->valence= ep->valence;

  /* beware: f(p) = Nv = 0
   *         Nv = p; f(Nv) --> this call would destroy p [ isclone ] */
  ep->value = (flag == COPY_VAL)? gclone(x):
                                  (x && isclone(x))? gcopy(x): x;
  /* Do this last. In case the clone is <C-C>'ed before completion ! */
  ep->pvalue= (char*)v;
  ep->valence=EpVAR;
}

/* kill ep->value and replace by preceding one, poped from value stack */
static void
pop_val(entree *ep)
{
  var_cell *v = (var_cell*) ep->pvalue;
  if (v != INITIAL)
  {
    GEN old_val = (GEN) ep->value; /* protect against SIGINT */
    ep->value  = v->value;
    if (v->flag == COPY_VAL) gunclone_deep(old_val);
    ep->pvalue = (char*) v->prev;
    ep->valence=v->valence;
    pari_free((void*)v);
  }
}

void
freeep(entree *ep)
{
  if (EpSTATIC(ep)) return; /* gp function loaded at init time */
  if (ep->help) {pari_free((void*)ep->help); ep->help=NULL;}
  if (ep->code) {pari_free((void*)ep->code); ep->code=NULL;}
  switch(EpVALENCE(ep))
  {
    case EpVAR:
      while (ep->pvalue!=INITIAL) pop_val(ep);
      break;
    case EpALIAS:
      killblock((GEN)ep->value); ep->value=NULL; break;
  }
}

INLINE void
pushvalue(entree *ep, GEN x) {
  new_val_cell(ep, x, COPY_VAL);
}

INLINE void
zerovalue (entree *ep)
{
  var_cell *v = (var_cell*) pari_malloc(sizeof(var_cell));
  v->value  = (GEN)ep->value;
  v->prev   = (var_cell*) ep->pvalue;
  v->flag   = PUSH_VAL;
  v->valence= ep->valence;
  ep->value = gen_0;
  ep->pvalue= (char*)v;
  ep->valence=EpVAR;
}


/* as above IF ep->value was PUSHed, or was created after block number 'loc'
   return 0 if not deleted, 1 otherwise [for recover()] */
int
pop_val_if_newer(entree *ep, long loc)
{
  var_cell *v = (var_cell*) ep->pvalue;

  if (v == INITIAL) return 0;
  if (v->flag == COPY_VAL && !pop_entree_block(ep, loc)) return 0;
  ep->value = v->value;
  ep->pvalue= (char*) v->prev;
  ep->valence=v->valence;
  pari_free((void*)v); return 1;
}

/* set new value of ep directly to val (COPY), do not save last value unless
 * it's INITIAL. */
void
changevalue(entree *ep, GEN x)
{
  var_cell *v = (var_cell*) ep->pvalue;
  if (v == INITIAL) new_val_cell(ep, x, COPY_VAL);
  else
  {
    GEN old_val = (GEN) ep->value; /* beware: gunclone_deep may destroy old x */
    ep->value = (void *) gclone(x);
    if (v->flag == COPY_VAL) gunclone_deep(old_val); else v->flag = COPY_VAL;
  }
}

INLINE GEN
copyvalue(entree *ep)
{
  var_cell *v = (var_cell*) ep->pvalue;
  if (v && v->flag != COPY_VAL)
  {
    ep->value = (void*) gclone((GEN)ep->value);
    v->flag = COPY_VAL;
  }
  return (GEN) ep->value;
}

INLINE void
err_var(GEN x) { pari_err_TYPE("evaluator [variable name expected]", x); }

enum chk_VALUE { chk_ERROR, chk_NOCREATE, chk_CREATE };

INLINE void
checkvalue(entree *ep, enum chk_VALUE flag)
{
  if (MT_IS_THREAD)
    pari_err(e_MISC,"mt: global variable not supported: %s",ep->name);
  if (ep->valence==EpNEW)
    switch(flag)
    {
      case chk_ERROR:
        /* Do nothing until we can report a meaningful error message
           The extra variable will be cleaned-up anyway */
      case chk_CREATE:
        pari_var_create(ep);
        ep->valence = EpVAR;
        ep->value = initial_value(ep);
        break;
      case chk_NOCREATE:
        break;
    }
  else if (ep->valence!=EpVAR)
    err_var(strtoGENstr(ep->name));
}

INLINE GEN
checkvalueptr(entree *ep)
{
  checkvalue(ep, chk_NOCREATE);
  return ep->valence==EpNEW? gen_0: (GEN)ep->value;
}

/* make GP variables safe for avma = top */
static void
lvar_make_safe(void)
{
  long n;
  entree *ep;
  for (n = 0; n < functions_tblsz; n++)
    for (ep = functions_hash[n]; ep; ep = ep->next)
      if (EpVALENCE(ep) == EpVAR)
      { /* make sure ep->value is a COPY */
        var_cell *v = (var_cell*)ep->pvalue;
        if (v && v->flag == PUSH_VAL) {
          GEN x = (GEN)ep->value;
          if (x) changevalue(ep, (GEN)ep->value); else pop_val(ep);
        }
      }
}

static void
check_array_index(long c, long l)
{
  if (c < 1) pari_err_COMPONENT("", "<", gen_1, stoi(c));
  if (c >= l) pari_err_COMPONENT("", ">", stoi(l-1), stoi(c));
}

GEN*
safegel(GEN x, long l)
{
  if (!is_matvec_t(typ(x)))
    pari_err_TYPE("safegel",x);
  check_array_index(l, lg(x));
  return &(gel(x,l));
}

GEN*
safelistel(GEN x, long l)
{
  GEN d;
  if (typ(x)!=t_LIST || list_typ(x)!=t_LIST_RAW)
    pari_err_TYPE("safelistel",x);
  d = list_data(x);
  check_array_index(l, lg(d));
  return &(gel(d,l));
}

long*
safeel(GEN x, long l)
{
  if (typ(x)!=t_VECSMALL)
    pari_err_TYPE("safeel",x);
  check_array_index(l, lg(x));
  return &(x[l]);
}

GEN*
safegcoeff(GEN x, long a, long b)
{
  if (typ(x)!=t_MAT) pari_err_TYPE("safegcoeff", x);
  check_array_index(b, lg(x));
  check_array_index(a, lg(gel(x,b)));
  return &(gcoeff(x,a,b));
}

typedef struct matcomp
{
  GEN *ptcell;
  GEN parent;
  int full_col, full_row;
} matcomp;

typedef struct gp_pointer
{
  matcomp c;
  GEN x, ox;
  entree *ep;
  long vn;
  long sp;
} gp_pointer;


/* assign res at *pt in "simple array object" p and return it, or a copy.*/
static void
change_compo(matcomp *c, GEN res)
{
  GEN p = c->parent, *pt = c->ptcell;
  long i, t;

  if (typ(p) == t_VECSMALL)
  {
    if (typ(res) != t_INT || is_bigint(res))
      pari_err_TYPE("t_VECSMALL assignment", res);
    *pt = (GEN)itos(res); return;
  }
  t = typ(res);
  if (c->full_row)
  {
    if (t != t_VEC) pari_err_TYPE("matrix row assignment", res);
    if (lg(res) != lg(p)) pari_err_DIM("matrix row assignment");
    for (i=1; i<lg(p); i++)
    {
      GEN p1 = gcoeff(p,c->full_row,i); /* Protect against SIGINT */
      gcoeff(p,c->full_row,i) = gclone(gel(res,i));
      if (isclone(p1)) gunclone_deep(p1);
    }
    return;
  }
  if (c->full_col)
  {
    if (t != t_COL) pari_err_TYPE("matrix col assignment", res);
    if (lg(res) != lg(*pt)) pari_err_DIM("matrix col assignment");
  }

  res = gclone(res);
  gunclone_deep(*pt);
  *pt = res;
}

/***************************************************************************
 **                                                                       **
 **                           Byte-code evaluator                         **
 **                                                                       **
 ***************************************************************************/

struct var_lex
{
  long flag;
  GEN value;
};

struct trace
{
  long pc;
  GEN closure;
};

static THREAD long sp, rp, dbg_level;
static THREAD long *st, *precs;
static THREAD gp_pointer *ptrs;
static THREAD entree **lvars;
static THREAD struct var_lex *var;
static THREAD struct trace *trace;
static THREAD pari_stack s_st, s_ptrs, s_var, s_lvars, s_trace, s_prec;

static void
changelex(long vn, GEN x)
{
  struct var_lex *v=var+s_var.n+vn;
  GEN old_val = v->value;
  v->value = gclone(x);
  if (v->flag == COPY_VAL) gunclone_deep(old_val); else v->flag = COPY_VAL;
}

INLINE GEN
copylex(long vn)
{
  struct var_lex *v = var+s_var.n+vn;
  if (v->flag!=COPY_VAL)
  {
    v->value = gclone(v->value);
    v->flag  = COPY_VAL;
  }
  return v->value;
}

INLINE void
pushlex(long vn, GEN x)
{
  struct var_lex *v=var+s_var.n+vn;
  v->flag  = PUSH_VAL;
  v->value = x;
}

INLINE void
freelex(void)
{
  struct var_lex *v=var+s_var.n-1;
  s_var.n--;
  if (v->flag == COPY_VAL) gunclone_deep(v->value);
}

INLINE void
restore_vars(long nbmvar, long nblvar)
{
  long j;
  for(j=1;j<=nbmvar;j++)
    freelex();
  for(j=1;j<=nblvar;j++)
    { s_lvars.n--; pop_val(lvars[s_lvars.n]); }
}

INLINE void
restore_trace(long nbtrace)
{
  long j;
  for(j=1;j<=nbtrace;j++)
  {
    GEN C = trace[s_trace.n-j].closure;
    if (isclone(C)) gunclone(C);
  }
  s_trace.n-=nbtrace;
}

INLINE long
trace_push(long pc, GEN C)
{
  long tr;
  BLOCK_SIGINT_START
  tr = pari_stack_new(&s_trace);
  trace[tr].pc = pc;
  trace[tr].closure = C;
  BLOCK_SIGINT_END
  return tr;
}

void
push_lex(GEN a, GEN C)
{
  long vn=pari_stack_new(&s_var);
  struct var_lex *v=var+vn;
  v->flag  = PUSH_VAL;
  v->value = a;
  if (C) (void) trace_push(-1, C);
}

GEN
get_lex(long vn)
{
  struct var_lex *v=var+s_var.n+vn;
  return v->value;
}

void
set_lex(long vn, GEN x)
{
  struct var_lex *v=var+s_var.n+vn;
  if (v->flag == COPY_VAL) { gunclone_deep(v->value); v->flag = PUSH_VAL; }
  v->value = x;
}

void
pop_lex(long n)
{
  long j;
  for(j=1; j<=n; j++)
    freelex();
  s_trace.n--;
}

static THREAD pari_stack s_relocs;
static THREAD entree **relocs;

void
pari_init_evaluator(void)
{
  sp=0;
  pari_stack_init(&s_st,sizeof(*st),(void**)&st);
  pari_stack_alloc(&s_st,32);
  s_st.n=s_st.alloc;
  rp=0;
  pari_stack_init(&s_ptrs,sizeof(*ptrs),(void**)&ptrs);
  pari_stack_alloc(&s_ptrs,16);
  s_ptrs.n=s_ptrs.alloc;
  pari_stack_init(&s_var,sizeof(*var),(void**)&var);
  pari_stack_init(&s_lvars,sizeof(*lvars),(void**)&lvars);
  pari_stack_init(&s_trace,sizeof(*trace),(void**)&trace);
  br_res = NULL;
  pari_stack_init(&s_relocs,sizeof(*relocs),(void**)&relocs);
  pari_stack_init(&s_prec,sizeof(*precs),(void**)&precs);
}
void
pari_close_evaluator(void)
{
  pari_stack_delete(&s_st);
  pari_stack_delete(&s_ptrs);
  pari_stack_delete(&s_var);
  pari_stack_delete(&s_lvars);
  pari_stack_delete(&s_trace);
  pari_stack_delete(&s_relocs);
  pari_stack_delete(&s_prec);
}

static gp_pointer *
new_ptr(void)
{
  if (rp==s_ptrs.n-1)
  {
    long i;
    gp_pointer *old = ptrs;
    (void)pari_stack_new(&s_ptrs);
    if (old != ptrs)
      for(i=0; i<rp; i++)
      {
        gp_pointer *g = &ptrs[i];
        if(g->sp >= 0) gel(st,g->sp) = (GEN) &(g->x);
      }
  }
  return &ptrs[rp++];
}

void
push_localprec(long p)
{
  long n = pari_stack_new(&s_prec);
  precs[n] = prec2nbits(p);
}

void
push_localbitprec(long p)
{
  long n = pari_stack_new(&s_prec);
  precs[n] = p;
}

void
pop_localprec(void)
{
  s_prec.n--;
}

long
get_localbitprec(void)
{
  return s_prec.n? precs[s_prec.n-1]: precreal;
}

long
get_localprec(void)
{
  return nbits2prec(get_localbitprec());
}

void
localprec(long p)
{
  long pmax = prec2ndec(LGBITS);
  if (p < 1) pari_err_DOMAIN("localprec", "p", "<", gen_1, stoi(p));
  if (p > pmax)
    pari_err_DOMAIN("localprec", "p", ">", utoi(pmax), stoi(p));
  push_localprec(ndec2prec(p));
}

void
localbitprec(long p)
{
  if (p < 1) pari_err_DOMAIN("localprec", "p", "<", gen_1, stoi(p));
  if (p > (long)LGBITS)
    pari_err_DOMAIN("localbitprec", "p", ">", utoi(LGBITS), stoi(p));
  push_localbitprec(p);
}

INLINE GEN
copyupto(GEN z, GEN t)
{
  if (is_universal_constant(z) || (z>(GEN)pari_mainstack->bot && z<=t))
    return z;
  else
    return gcopy(z);
}

static void closure_eval(GEN C);

INLINE GEN
closure_return(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  if (br_status)
  {
    GEN z;
    avma=ltop;
    z=br_res?gcopy(br_res):gnil;
    reset_break();
    return z;
  }
  return gerepileupto(ltop,gel(st,--sp));
}

/* for the break_loop debugger. Not memory clean */
GEN
closure_evalbrk(GEN C, long *status)
{
  closure_eval(C);
  *status = br_status;
  if (br_status)
  {
    GEN z = br_res? gcopy(br_res): gnil;
    reset_break();
    return z;
  }
  return gel(st,--sp);
}

INLINE long
closure_varn(GEN x)
{
  if (!x) return -1;
  if (!gequalX(x)) err_var(x);
  return varn(x);
}

INLINE void
closure_castgen(GEN z, long mode)
{
  switch (mode)
  {
  case Ggen:
    gel(st,sp++)=z;
    break;
  case Gsmall:
    st[sp++]=gtos(z);
    break;
  case Gusmall:
    st[sp++]=gtou(z);
    break;
  case Gvar:
    st[sp++]=closure_varn(z);
    break;
  case Gvoid:
    break;
  default:
    pari_err_BUG("closure_castgen, type unknown");
  }
}

INLINE void
closure_castlong(long z, long mode)
{
  switch (mode)
  {
  case Gsmall:
    st[sp++]=z;
    break;
  case Gusmall:
    if (z < 0)
      pari_err_TYPE("stou [integer >=0 expected]", stoi(z));
    st[sp++]=(ulong) z;
    break;
  case Ggen:
    gel(st,sp++)=stoi(z);
    break;
  case Gvar:
    err_var(stoi(z));
  case Gvoid:
    break;
  default:
    pari_err_BUG("closure_castlong, type unknown");
  }
}

const char *
closure_func_err(void)
{
  long fun=s_trace.n-1, pc;
  const char *code;
  GEN C, oper;
  if (fun < 0 || trace[fun].pc < 0) return NULL;
  pc = trace[fun].pc; C  = trace[fun].closure;
  code = closure_codestr(C); oper = closure_get_oper(C);
  if (code[pc]==OCcallgen || code[pc]==OCcallgen2 ||
      code[pc]==OCcallint || code[pc]==OCcalllong || code[pc]==OCcallvoid)
    return ((entree*)oper[pc])->name;
  return NULL;
}

/* return the next label for the call chain debugger closure_err(),
 * incorporating the name of the user of member function. Return NULL for an
 * anonymous (inline) closure. */
static char *
get_next_label(const char *s, int member, char **next_fun)
{
  const char *v, *t = s+1;
  char *u, *next_label;

  if (!is_keyword_char(*s)) return NULL;
  while (is_keyword_char(*t)) t++;
  /* e.g. (x->1/x)(0) instead of (x)->1/x */
  if (t[0] == '-' && t[1] == '>') return NULL;
  next_label = (char*)pari_malloc(t - s + 32);
  sprintf(next_label, "in %sfunction ", member? "member ": "");
  u = *next_fun = next_label + strlen(next_label);
  v = s;
  while (v < t) *u++ = *v++;
  *u++ = 0; return next_label;
}

static const char *
get_arg_name(GEN C, long i)
{
  GEN d = closure_get_dbg(C), frpc = gel(d,2), fram = gel(d,3);
  long j, l = lg(frpc);
  for (j=1; j<l; j++)
    if (frpc[j]==1 && i<lg(gel(fram,j)))
      return ((entree*)mael(fram,j,i))->name;
  return "(unnamed)";
}

void
closure_err(long level)
{
  GEN base;
  const long lastfun = s_trace.n - 1 - level;
  char *next_label, *next_fun;
  long i = maxss(0, lastfun - 19);
  if (lastfun < 0) return; /*e.g. when called by gp_main_loop's simplify */
  if (i > 0) while (lg(trace[i].closure)==6) i--;
  base = closure_get_text(trace[i].closure); /* gcc -Wall*/
  next_label = pari_strdup(i == 0? "at top-level": "[...] at");
  next_fun = next_label;
  for (; i <= lastfun; i++)
  {
    GEN C = trace[i].closure;
    if (lg(C) >= 7) base=closure_get_text(C);
    if ((i==lastfun || lg(trace[i+1].closure)>=7))
    {
      GEN dbg = gel(closure_get_dbg(C),1);
      /* After a SIGINT, pc can be slightly off: ensure 0 <= pc < lg() */
      long pc = minss(lg(dbg)-1, trace[i].pc>=0 ? trace[i].pc: 1);
      long offset = pc? dbg[pc]: 0;
      int member;
      const char *s, *sbase;
      if (typ(base)!=t_VEC) sbase = GSTR(base);
      else if (offset>=0)   sbase = GSTR(gel(base,2));
      else { sbase = GSTR(gel(base,1)); offset += strlen(sbase); }
      s = sbase + offset;
      member = offset>0 && (s[-1] == '.');
      /* avoid "in function foo: foo" */
      if (!next_fun || strcmp(next_fun, s)) {
        print_errcontext(pariErr, next_label, s, sbase);
        out_putc(pariErr, '\n');
      }
      pari_free(next_label);
      if (i == lastfun) break;

      next_label = get_next_label(s, member, &next_fun);
      if (!next_label) {
        next_label = pari_strdup("in anonymous function");
        next_fun = NULL;
      }
    }
  }
}

GEN
pari_self(void)
{
  long fun = s_trace.n - 1;
  if (fun > 0) while (lg(trace[fun].closure)==6) fun--;
  return fun >= 0 ? trace[fun].closure: NULL;
}

long
closure_context(long start, long level)
{
  const long lastfun = s_trace.n - 1 - level;
  long i, fun = lastfun;
  if (fun<0) return lastfun;
  while (fun>start && lg(trace[fun].closure)==6) fun--;
  for (i=fun; i <= lastfun; i++)
    push_frame(trace[i].closure, trace[i].pc,0);
  for (  ; i < s_trace.n; i++)
    push_frame(trace[i].closure, trace[i].pc,1);
  return s_trace.n-level;
}

INLINE void
st_alloc(long n)
{
  if (sp+n>s_st.n)
  {
    pari_stack_alloc(&s_st,n+16);
    s_st.n=s_st.alloc;
    if (DEBUGMEM>=2) pari_warn(warner,"doubling evaluator stack");
  }
}

INLINE void
ptr_proplock(gp_pointer *g, GEN C)
{
  g->x = C;
  if (isclone(g->x))
  {
    clone_unlock_deep(g->ox);
    g->ox = g->x;
    ++bl_refc(g->ox);
  }
}

static void
closure_eval(GEN C)
{
  const char *code=closure_codestr(C);
  GEN oper=closure_get_oper(C);
  GEN data=closure_get_data(C);
  long loper=lg(oper);
  long saved_sp=sp-closure_arity(C);
  long saved_rp=rp, saved_prec=s_prec.n;
  long j, nbmvar=0, nblvar=0;
  long pc, t;
#ifdef STACK_CHECK
  GEN stackelt;
  if (PARI_stack_limit && (void*) &stackelt <= PARI_stack_limit)
    pari_err(e_MISC, "deep recursion");
#endif
  clone_lock(C);
  t = trace_push(0, C);
  if (lg(C)==8)
  {
    GEN z=closure_get_frame(C);
    long l=lg(z)-1;
    pari_stack_alloc(&s_var,l);
    s_var.n+=l;
    nbmvar+=l;
    for(j=1;j<=l;j++)
    {
      var[s_var.n-j].flag=PUSH_VAL;
      var[s_var.n-j].value=gel(z,j);
    }
  }

  for(pc=1;pc<loper;pc++)
  {
    op_code opcode=(op_code) code[pc];
    long operand=oper[pc];
    if (sp<0) pari_err_BUG("closure_eval, stack underflow");
    st_alloc(16);
    trace[t].pc = pc;
    CHECK_CTRLC
    switch(opcode)
    {
    case OCpushlong:
      st[sp++]=operand;
      break;
    case OCpushgnil:
      gel(st,sp++)=gnil;
      break;
    case OCpushgen:
      gel(st,sp++)=gel(data,operand);
      break;
    case OCpushreal:
      gel(st,sp++)=strtor(GSTR(data[operand]),get_localprec());
      break;
    case OCpushstoi:
      gel(st,sp++)=stoi(operand);
      break;
    case OCpushvar:
      {
        entree *ep = (entree *)operand;
        gel(st,sp++)=pol_x(pari_var_create(ep));
        break;
      }
    case OCpushdyn:
      {
        entree *ep = (entree *)operand;
        checkvalue(ep, chk_CREATE);
        gel(st,sp++)=(GEN)ep->value;
        break;
      }
    case OCpushlex:
      gel(st,sp++)=var[s_var.n+operand].value;
      break;
    case OCsimpleptrdyn:
      {
        gp_pointer *g = new_ptr();
        g->vn=0;
        g->ep = (entree*) operand;
        g->x = checkvalueptr(g->ep);
        g->ox = g->x; clone_lock(g->ox);
        g->sp = sp;
        gel(st,sp++) = (GEN)&(g->x);
        break;
      }
    case OCsimpleptrlex:
      {
        gp_pointer *g = new_ptr();
        g->vn=operand;
        g->ep=(entree *)0x1L;
        g->x = (GEN) var[s_var.n+operand].value;
        g->ox = g->x; clone_lock(g->ox);
        g->sp = sp;
        gel(st,sp++) = (GEN)&(g->x);
        break;
      }
    case OCnewptrdyn:
      {
        entree *ep = (entree *)operand;
        gp_pointer *g = new_ptr();
        matcomp *C;
        checkvalue(ep, chk_ERROR);
        g->sp = -1;
        g->x = copyvalue(ep);
        g->ox = g->x; clone_lock(g->ox);
        g->vn=0;
        g->ep=NULL;
        C=&g->c;
        C->full_col = C->full_row = 0;
        C->parent   = (GEN)    g->x;
        C->ptcell   = (GEN *) &g->x;
        break;
      }
    case OCnewptrlex:
      {
        gp_pointer *g = new_ptr();
        matcomp *C;
        g->sp = -1;
        g->x = copylex(operand);
        g->ox = g->x; clone_lock(g->ox);
        g->vn=0;
        g->ep=NULL;
        C=&g->c;
        C->full_col = C->full_row = 0;
        C->parent   = (GEN)     g->x;
        C->ptcell   = (GEN *) &(g->x);
        break;
      }
    case OCpushptr:
      {
        gp_pointer *g = &ptrs[rp-1];
        g->sp = sp;
        gel(st,sp++) = (GEN)&(g->x);
      }
      break;
    case OCendptr:
      for(j=0;j<operand;j++)
      {
        gp_pointer *g = &ptrs[--rp];
        if (g->ep)
        {
          if (g->vn)
            changelex(g->vn, g->x);
          else
            changevalue(g->ep, g->x);
        }
        else change_compo(&(g->c), g->x);
        clone_unlock_deep(g->ox);
      }
      break;
    case OCstoredyn:
      {
        entree *ep = (entree *)operand;
        checkvalue(ep, chk_NOCREATE);
        changevalue(ep, gel(st,--sp));
        break;
      }
    case OCstorelex:
      changelex(operand,gel(st,--sp));
      break;
    case OCstoreptr:
      {
        gp_pointer *g = &ptrs[--rp];
        change_compo(&(g->c), gel(st,--sp));
        clone_unlock_deep(g->ox);
        break;
      }
    case OCstackgen:
      {
        GEN z = gerepileupto(st[sp-2],gel(st,sp-1));
        gmael(st,sp-3,operand) = copyupto(z,gel(st,sp-2));
        st[sp-2] = avma;
        sp--;
        break;
      }
    case OCprecreal:
      st[sp++]=get_localprec();
      break;
    case OCbitprecreal:
      st[sp++]=get_localbitprec();
      break;
    case OCprecdl:
      st[sp++]=precdl;
      break;
    case OCavma:
      st[sp++]=avma;
      break;
    case OCcowvardyn:
      {
        entree *ep = (entree *)operand;
        checkvalue(ep, chk_ERROR);
        (void)copyvalue(ep);
        break;
      }
    case OCcowvarlex:
      (void)copylex(operand);
      break;
    case OCstoi:
      gel(st,sp-1)=stoi(st[sp-1]);
      break;
    case OCutoi:
      gel(st,sp-1)=utoi(st[sp-1]);
      break;
    case OCitos:
      st[sp+operand]=gtos(gel(st,sp+operand));
      break;
    case OCitou:
      st[sp+operand]=gtou(gel(st,sp+operand));
      break;
    case OCtostr:
      {
        GEN z = gel(st,sp+operand);
        st[sp+operand] = (long)GENtostr_unquoted(z);
        break;
      }
    case OCvarn:
      st[sp+operand] = closure_varn(gel(st,sp+operand));
      break;
    case OCcopy:
      gel(st,sp-1) = gcopy(gel(st,sp-1));
      break;
    case OCgerepile:
    {
      pari_sp av;
      GEN x;
      sp--;
      av = st[sp-1];
      x = gel(st,sp);
      if (isonstack(x))
      {
        pari_sp av2 = (pari_sp)(x + lg(x));
        if ((long) (av - av2) > 1000000L)
        {
          if (DEBUGMEM>=2)
            pari_warn(warnmem,"eval: recovering %ld bytes", av - av2);
          x = gerepileupto(av, x);
        }
      } else avma = av;
      gel(st,sp-1) = x;
      break;
    }
    case OCcopyifclone:
      if (isclone(gel(st,sp-1)))
        gel(st,sp-1) = gcopy(gel(st,sp-1));
      break;
    case OCcompo1:
      {
        GEN  p=gel(st,sp-2);
        long c=st[sp-1];
        sp-=2;
        switch(typ(p))
        {
        case t_VEC: case t_COL:
          check_array_index(c, lg(p));
          closure_castgen(gel(p,c),operand);
          break;
        case t_LIST:
          {
            long lx;
            if (list_typ(p)!=t_LIST_RAW)
              pari_err_TYPE("_[_] OCcompo1 [not a vector]", p);
            p = list_data(p); lx = p? lg(p): 1;
            check_array_index(c, lx);
            closure_castgen(gel(p,c),operand);
            break;
          }
        case t_VECSMALL:
          check_array_index(c,lg(p));
          closure_castlong(p[c],operand);
          break;
        default:
          pari_err_TYPE("_[_] OCcompo1 [not a vector]", p);
          break;
        }
        break;
      }
    case OCcompo1ptr:
      {
        long c=st[sp-1];
        long lx;
        gp_pointer *g = &ptrs[rp-1];
        matcomp *C=&g->c;
        GEN p = g->x;
        sp--;
        switch(typ(p))
        {
        case t_VEC: case t_COL:
          check_array_index(c, lg(p));
          C->ptcell = (GEN *) p+c;
          ptr_proplock(g, *(C->ptcell));
          break;
        case t_VECSMALL:
          check_array_index(c, lg(p));
          C->ptcell = (GEN *) p+c;
          g->x = stoi(p[c]);
          break;
        case t_LIST:
          if (list_typ(p)!=t_LIST_RAW)
            pari_err_TYPE("&_[_] OCcompo1 [not a vector]", p);
          p = list_data(p); lx = p? lg(p): 1;
          check_array_index(c,lx);
          C->ptcell = (GEN *) p+c;
          ptr_proplock(g, *(C->ptcell));
          break;
        default:
          pari_err_TYPE("&_[_] OCcompo1ptr [not a vector]", p);
        }
        C->parent   = p;
        break;
      }
    case OCcompo2:
      {
        GEN  p=gel(st,sp-3);
        long c=st[sp-2];
        long d=st[sp-1];
        if (typ(p)!=t_MAT) pari_err_TYPE("_[_,_] OCcompo2 [not a matrix]", p);
        check_array_index(d, lg(p));
        check_array_index(c, lg(gel(p,d)));
        sp-=3;
        closure_castgen(gcoeff(p,c,d),operand);
        break;
      }
    case OCcompo2ptr:
      {
        long c=st[sp-2];
        long d=st[sp-1];
        gp_pointer *g = &ptrs[rp-1];
        matcomp *C=&g->c;
        GEN p = g->x;
        sp-=2;
        if (typ(p)!=t_MAT)
          pari_err_TYPE("&_[_,_] OCcompo2ptr [not a matrix]", p);
        check_array_index(d, lg(p));
        check_array_index(c, lg(gel(p,d)));
        C->ptcell = (GEN *) gel(p,d)+c;
        C->parent   = p;
        ptr_proplock(g, *(C->ptcell));
        break;
      }
    case OCcompoC:
      {
        GEN  p=gel(st,sp-2);
        long c=st[sp-1];
        if (typ(p)!=t_MAT)
          pari_err_TYPE("_[,_] OCcompoC [not a matrix]", p);
        check_array_index(c, lg(p));
        sp--;
        gel(st,sp-1) = gel(p,c);
        break;
      }
    case OCcompoCptr:
      {
        long c=st[sp-1];
        gp_pointer *g = &ptrs[rp-1];
        matcomp *C=&g->c;
        GEN p = g->x;
        sp--;
        if (typ(p)!=t_MAT)
          pari_err_TYPE("&_[,_] OCcompoCptr [not a matrix]", p);
        check_array_index(c, lg(p));
        C->ptcell = (GEN *) p+c;
        C->full_col = c;
        C->parent   = p;
        ptr_proplock(g, *(C->ptcell));
        break;
      }
    case OCcompoL:
      {
        GEN  p=gel(st,sp-2);
        long r=st[sp-1];
        sp--;
        if (typ(p)!=t_MAT)
          pari_err_TYPE("_[_,] OCcompoL [not a matrix]", p);
        check_array_index(r,lg(p) == 1? 1: lgcols(p));
        gel(st,sp-1) = row(p,r);
        break;
      }
    case OCcompoLptr:
      {
        long r=st[sp-1];
        gp_pointer *g = &ptrs[rp-1];
        matcomp *C=&g->c;
        GEN p = g->x, p2;
        sp--;
        if (typ(p)!=t_MAT)
          pari_err_TYPE("&_[_,] OCcompoLptr [not a matrix]", p);
        check_array_index(r,lg(p) == 1? 1: lgcols(p));
        p2 = rowcopy(p,r);
        C->full_row = r; /* record row number */
        C->ptcell = &p2;
        C->parent   = p;
        g->x = p2;
        break;
      }
    case OCdefaultarg:
      if (var[s_var.n+operand].flag==DEFAULT_VAL)
      {
        GEN z = gel(st,sp-1);
        if (typ(z)==t_CLOSURE)
        {
          pushlex(operand, closure_evalnobrk(z));
          copylex(operand);
        }
        else
          pushlex(operand, z);
      }
      sp--;
      break;
    case OClocalvar:
      {
        long n = pari_stack_new(&s_lvars);
        entree *ep = (entree *)operand;
        checkvalue(ep, chk_NOCREATE);
        lvars[n] = ep;
        nblvar++;
        pushvalue(ep,gel(st,--sp));
        break;
      }
    case OClocalvar0:
      {
        long n = pari_stack_new(&s_lvars);
        entree *ep = (entree *)operand;
        checkvalue(ep, chk_NOCREATE);
        lvars[n] = ep;
        nblvar++;
        zerovalue(ep);
        break;
      }

#define EVAL_f(f) \
  switch (ep->arity) \
  { \
    case 0: f(); break; \
    case 1: sp--; f(st[sp]); break; \
    case 2: sp-=2; f(st[sp],st[sp+1]); break; \
    case 3: sp-=3; f(st[sp],st[sp+1],st[sp+2]); break; \
    case 4: sp-=4; f(st[sp],st[sp+1],st[sp+2],st[sp+3]); break; \
    case 5: sp-=5; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4]); break; \
    case 6: sp-=6; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5]); break; \
    case 7: sp-=7; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6]); break; \
    case 8: sp-=8; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7]); break; \
    case 9: sp-=9; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8]); break; \
    case 10: sp-=10; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9]); break; \
    case 11: sp-=11; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10]); break; \
    case 12: sp-=12; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11]); break; \
    case 13: sp-=13; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12]); break; \
    case 14: sp-=14; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13]); break; \
    case 15: sp-=15; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14]); break; \
    case 16: sp-=16; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15]); break; \
    case 17: sp-=17; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16]); break; \
    case 18: sp-=18; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16],st[sp+17]); break; \
    case 19: sp-=19; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16],st[sp+17],st[sp+18]); break; \
    case 20: sp-=20; f(st[sp],st[sp+1],st[sp+2],st[sp+3],st[sp+4],st[sp+5],st[sp+6],st[sp+7],st[sp+8],st[sp+9],st[sp+10],st[sp+11],st[sp+12],st[sp+13],st[sp+14],st[sp+15],st[sp+16],st[sp+17],st[sp+18],st[sp+19]); break; \
    default: \
      pari_err_IMPL("functions with more than 20 parameters");\
      goto endeval; /*LCOV_EXCL_LINE*/ \
  }

    case OCcallgen:
      {
        entree *ep = (entree *)operand;
        GEN res;
        /* Macro Madness : evaluate function ep->value on arguments
         * st[sp-ep->arity .. sp]. Set res = result. */
        EVAL_f(res = ((GEN (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        gel(st,sp++)=res;
        break;
      }
    case OCcallgen2: /*same for ep->arity = 2. Is this optimization worth it ?*/
      {
        entree *ep = (entree *)operand;
        GEN res;
        sp-=2;
        res = ((GEN (*)(GEN,GEN))ep->value)(gel(st,sp),gel(st,sp+1));
        if (br_status) goto endeval;
        gel(st,sp++)=res;
        break;
      }
    case OCcalllong:
      {
        entree *ep = (entree *)operand;
        long res;
        EVAL_f(res = ((long (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        st[sp++] = res;
        break;
      }
    case OCcallint:
      {
        entree *ep = (entree *)operand;
        long res;
        EVAL_f(res = ((int (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        st[sp++] = res;
        break;
      }
    case OCcallvoid:
      {
        entree *ep = (entree *)operand;
        EVAL_f(((void (*)(ANYARG))ep->value));
        if (br_status) goto endeval;
        break;
      }
#undef EVAL_f

    case OCcalluser:
      {
        long n=operand;
        GEN fun = gel(st,sp-1-n);
        long arity, isvar;
        GEN z;
        if (typ(fun)!=t_CLOSURE) pari_err(e_NOTFUNC, fun);
        isvar = closure_is_variadic(fun);
        arity = closure_arity(fun);
        if (!isvar || n < arity)
        {
          st_alloc(arity-n);
          if (n>arity)
            pari_err(e_MISC,"too many parameters in user-defined function call");
          for (j=n+1;j<=arity;j++)
            gel(st,sp++)=0;
          if (isvar) gel(st,sp-1) = cgetg(1,t_VEC);
        }
        else
        {
          GEN v;
          long j, m = n-arity+1;
          v = cgetg(m+1,t_VEC);
          sp-=m;
          for (j=1; j<=m; j++)
            gel(v,j) = gel(st,sp+j-1)? gcopy(gel(st,sp+j-1)): gen_0;
          gel(st,sp++)=v;
        }
        z = closure_return(fun);
        if (br_status) goto endeval;
        gel(st, sp-1) = z;
        break;
      }
    case OCnewframe:
      if (operand>0) nbmvar+=operand;
      else operand=-operand;
      pari_stack_alloc(&s_var,operand);
      s_var.n+=operand;
      for(j=1;j<=operand;j++)
      {
        var[s_var.n-j].flag=PUSH_VAL;
        var[s_var.n-j].value=gen_0;
      }
      break;
    case OCsaveframe:
      {
        GEN cl = (operand?gcopy:shallowcopy)(gel(st,sp-1));
        long l = lg(gel(cl,7));
        GEN  v = cgetg(l, t_VEC);
        for(j=1; j<l; j++)
        {
          GEN val = var[s_var.n-j].value;
          gel(v,j) = operand?gcopy(val):val;
        }
        gel(cl,7) = v;
        gel(st,sp-1) = cl;
      }
      break;
    case OCgetargs:
      pari_stack_alloc(&s_var,operand);
      s_var.n+=operand;
      nbmvar+=operand;
      sp-=operand;
      for (j=0;j<operand;j++)
      {
        if (gel(st,sp+j))
          pushlex(j-operand,gel(st,sp+j));
        else
        {
          var[s_var.n+j-operand].flag=DEFAULT_VAL;
          var[s_var.n+j-operand].value=gen_0;
        }
      }
      break;
    case OCcheckuserargs:
      for (j=0; j<operand; j++)
        if (var[s_var.n-operand+j].flag==DEFAULT_VAL)
          pari_err(e_MISC,"missing mandatory argument"
                   " '%s' in user function",get_arg_name(C,j+1));
      break;
    case OCcheckargs:
      for (j=sp-1;operand;operand>>=1UL,j--)
        if ((operand&1L) && gel(st,j)==NULL)
          pari_err(e_MISC,"missing mandatory argument");
      break;
    case OCcheckargs0:
      for (j=sp-1;operand;operand>>=1UL,j--)
        if ((operand&1L) && gel(st,j))
          pari_err(e_MISC,"argument type not implemented");
      break;
    case OCdefaultlong:
      sp--;
      if (st[sp+operand])
        st[sp+operand]=gtos(gel(st,sp+operand));
      else
        st[sp+operand]=st[sp];
      break;
    case OCdefaultulong:
      sp--;
      if (st[sp+operand])
        st[sp+operand]=gtou(gel(st,sp+operand));
      else
        st[sp+operand]=st[sp];
      break;
    case OCdefaultgen:
      sp--;
      if (!st[sp+operand])
        st[sp+operand]=st[sp];
      break;
    case OCvec:
      gel(st,sp++)=cgetg(operand,t_VEC);
      st[sp++]=avma;
      break;
    case OCcol:
      gel(st,sp++)=cgetg(operand,t_COL);
      st[sp++]=avma;
      break;
    case OCmat:
      {
        GEN z;
        long l=st[sp-1];
        z=cgetg(operand,t_MAT);
        for(j=1;j<operand;j++)
          gel(z,j) = cgetg(l,t_COL);
        gel(st,sp-1) = z;
        st[sp++]=avma;
      }
      break;
    case OCpop:
      sp-=operand;
      break;
    case OCdup:
      {
        long i, s=st[sp-1];
        st_alloc(operand);
        for(i=1;i<=operand;i++)
          st[sp++]=s;
      }
      break;
    }
  }
  if (0)
  {
endeval:
    sp = saved_sp;
    for(  ; rp>saved_rp ;  )
    {
      gp_pointer *g = &ptrs[--rp];
      clone_unlock_deep(g->ox);
    }
  }
  s_prec.n = saved_prec;
  s_trace.n--;
  restore_vars(nbmvar, nblvar);
  clone_unlock(C);
}

GEN
closure_evalgen(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  if (br_status) { avma=ltop; return NULL; }
  return gerepileupto(ltop,gel(st,--sp));
}

void
evalstate_save(struct pari_evalstate *state)
{
  state->avma = avma;
  state->sp   = sp;
  state->rp   = rp;
  state->prec = s_prec.n;
  state->var  = s_var.n;
  state->lvars= s_lvars.n;
  state->trace= s_trace.n;
  compilestate_save(&state->comp);
  mtstate_save(&state->pending_threads);
}

void
evalstate_restore(struct pari_evalstate *state)
{
  avma = state->avma;
  mtstate_restore(&state->pending_threads);
  sp = state->sp;
  rp = state->rp;
  s_prec.n = state->prec;
  restore_vars(s_var.n-state->var,s_lvars.n-state->lvars);
  restore_trace(s_trace.n-state->trace);
  reset_break();
  compilestate_restore(&state->comp);
}

GEN
evalstate_restore_err(struct pari_evalstate *state)
{
  GENbin* err = copy_bin(pari_err_last());
  evalstate_restore(state);
  return bin_copy(err);
}

void
evalstate_reset(void)
{
  mtstate_reset();
  sp = 0;
  rp = 0;
  dbg_level = 0;
  restore_vars(s_var.n, s_lvars.n);
  s_trace.n = 0;
  reset_break();
  compilestate_reset();
  parsestate_reset();
  avma = pari_mainstack->top;
}

void
evalstate_clone(void)
{
  long i;
  for (i = 1; i<=s_var.n; i++) copylex(-i);
  lvar_make_safe();
  for (i = 0; i< s_trace.n; i++)
  {
    GEN C = trace[i].closure;
    if (isonstack(C)) trace[i].closure = gclone(C);
  }
}

GEN
closure_trapgen(GEN C, long numerr)
{
  VOLATILE GEN x;
  struct pari_evalstate state;
  evalstate_save(&state);
  pari_CATCH(numerr) { x = (GEN)1L; }
  pari_TRY { x = closure_evalgen(C); } pari_ENDCATCH;
  if (x == (GEN)1L) evalstate_restore(&state);
  return x;
}

GEN
closure_evalnobrk(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  if (br_status) pari_err(e_MISC, "break not allowed here");
  return gerepileupto(ltop,gel(st,--sp));
}

void
closure_evalvoid(GEN C)
{
  pari_sp ltop=avma;
  closure_eval(C);
  avma=ltop;
}

GEN
closure_evalres(GEN C)
{
  return closure_return(C);
}

INLINE GEN
closure_returnupto(GEN C)
{
  pari_sp av=avma;
  return copyupto(closure_return(C),(GEN)av);
}

GEN
pareval_worker(GEN C)
{
  return closure_callgenall(C, 0);
}

GEN
pareval(GEN C)
{
  pari_sp av = avma;
  long l = lg(C), i;
  GEN worker;
  if (!is_vec_t(typ(C))) pari_err_TYPE("pareval",C);
  for (i=1; i<l; i++)
    if (typ(gel(C,i))!=t_CLOSURE)
      pari_err_TYPE("pareval",gel(C,i));
  worker = snm_closure(is_entry("_pareval_worker"), NULL);
  return gerepileupto(av, gen_parapply(worker, C));
}

GEN
parvector_worker(GEN i, GEN C)
{
  return closure_callgen1(C, i);
}

GEN
parfor_worker(GEN i, GEN C)
{
  retmkvec2(gcopy(i), closure_callgen1(C, i));
}

GEN
parvector(long n, GEN code)
{
  long i, pending = 0, workid;
  GEN worker = snm_closure(is_entry("_parvector_worker"), mkvec(code));
  GEN a, V, done;
  struct pari_mt pt;
  mt_queue_start_lim(&pt, worker, n);
  a = mkvec(cgetipos(3)); /* left on the stack */
  V = cgetg(n+1, t_VEC);
  for (i=1; i<=n || pending; i++)
  {
    mael(a,1,2) = i;
    mt_queue_submit(&pt, i, i<=n? a: NULL);
    done = mt_queue_get(&pt, &workid, &pending);
    if (done) gel(V,workid) = done;
  }
  mt_queue_end(&pt);
  return V;
}

GEN
parsum(GEN a, GEN b, GEN code, GEN x)
{
  pari_sp av = avma, av2;
  long pending = 0;
  GEN worker = snm_closure(is_entry("_parvector_worker"), mkvec(code));
  GEN done;
  struct pari_mt pt;
  if (typ(a) != t_INT) pari_err_TYPE("parsum",a);
  if (!x) x = gen_0;
  if (gcmp(b,a) < 0) return gcopy(x);

  mt_queue_start(&pt, worker);
  b = gfloor(b);
  a = mkvec(setloop(a));
  av2=avma;
  for (; cmpii(gel(a,1),b) <= 0 || pending; gel(a,1) = incloop(gel(a,1)))
  {
    mt_queue_submit(&pt, 0, cmpii(gel(a,1),b) <= 0? a: NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (done)
    {
      x = gadd(x, done);
      if (gc_needed(av2,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"sum");
        x = gerepileupto(av2,x);
      }
    }
  }
  mt_queue_end(&pt);
  return gerepilecopy(av, x);
}

void
parfor(GEN a, GEN b, GEN code, void *E, long call(void*, GEN, GEN))
{
  pari_sp av = avma, av2;
  long running, pending = 0;
  long status = br_NONE;
  GEN worker = snm_closure(is_entry("_parfor_worker"), mkvec(code));
  GEN done, stop = NULL;
  struct pari_mt pt;
  if (typ(a) != t_INT) pari_err_TYPE("parfor",a);
  if (b)
  {
    if (gcmp(b,a) < 0) return;
    if (typ(b) == t_INFINITY)
    {
      if (inf_get_sign(b) < 0) return;
      b = NULL;
    }
    else
      b = gfloor(b);
  }
  mt_queue_start(&pt, worker);
  a = mkvec(setloop(a));
  av2 = avma;
  while ((running = (!stop && (!b || cmpii(gel(a,1),b) <= 0))) || pending)
  {
    mt_queue_submit(&pt, 0, running ? a: NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (call && done && (!stop || cmpii(gel(done,1),stop) < 0))
      if (call(E, gel(done,1), gel(done,2)))
      {
        status = br_status;
        br_status = br_NONE;
        stop = gerepileuptoint(av2, gel(done,1));
      }
    gel(a,1) = incloop(gel(a,1));
    if (!stop) avma = av2;
  }
  avma = av2;
  mt_queue_end(&pt);
  br_status = status;
  avma = av;
}

static long
gp_evalvoid2(void *E, GEN x, GEN y)
{
  GEN code =(GEN) E;
  push_lex(x, code);
  push_lex(y, NULL);
  closure_evalvoid(code);
  pop_lex(2);
  return loop_break();
}

void
parfor0(GEN a, GEN b, GEN code, GEN code2)
{
  parfor(a, b, code, (void*)code2, code2 ? gp_evalvoid2: NULL);
}

void
parforprime(GEN a, GEN b, GEN code, void *E, long call(void*, GEN, GEN))
{
  pari_sp av = avma, av2;
  long running, pending = 0;
  long status = br_NONE;
  GEN worker = snm_closure(is_entry("_parfor_worker"), mkvec(code));
  GEN v, done, stop = NULL;
  struct pari_mt pt;
  forprime_t T;

  if (!forprime_init(&T, a,b)) { avma = av; return; }
  mt_queue_start(&pt, worker);
  v = mkvec(gen_0);
  av2 = avma;
  while ((running = (!stop && forprime_next(&T))) || pending)
  {
    gel(v, 1) = T.pp;
    mt_queue_submit(&pt, 0, running ? v: NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (call && done && (!stop || cmpii(gel(done,1),stop) < 0))
      if (call(E, gel(done,1), gel(done,2)))
      {
        status = br_status;
        br_status = br_NONE;
        stop = gerepileuptoint(av2, gel(done,1));
      }
    if (!stop) avma = av2;
  }
  avma = av2;
  mt_queue_end(&pt);
  br_status = status;
  avma = av;
}

void
parforprime0(GEN a, GEN b, GEN code, GEN code2)
{
  parforprime(a, b, code, (void*)code2, code2? gp_evalvoid2: NULL);
}

void
parforvec(GEN x, GEN code, long flag, void *E, long call(void*, GEN, GEN))
{
  pari_sp av = avma, av2;
  long running, pending = 0;
  long status = br_NONE;
  GEN worker = snm_closure(is_entry("_parfor_worker"), mkvec(code));
  GEN done, stop = NULL;
  struct pari_mt pt;
  forvec_t T;
  GEN a, v = gen_0;

  if (!forvec_init(&T, x, flag)) { avma = av; return; }
  mt_queue_start(&pt, worker);
  a = mkvec(gen_0);
  av2 = avma;
  while ((running = (!stop && v && (v = forvec_next(&T)))) || pending)
  {
    gel(a, 1) = v;
    mt_queue_submit(&pt, 0, running ? a: NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (call && done && (!stop || lexcmp(gel(done,1),stop) < 0))
      if (call(E, gel(done,1), gel(done,2)))
      {
        status = br_status;
        br_status = br_NONE;
        stop = gerepilecopy(av2, gel(done,1));
      }
    if (!stop) avma = av2;
  }
  avma = av2;
  mt_queue_end(&pt);
  br_status = status;
  avma = av;
}

void
parforvec0(GEN x, GEN code, GEN code2, long flag)
{
  parforvec(x, code, flag, (void*)code2, code2? gp_evalvoid2: NULL);
}

void
closure_callvoid1(GEN C, GEN x)
{
  long i, ar = closure_arity(C);
  gel(st,sp++) = x;
  for(i=2; i <= ar; i++) gel(st,sp++) = NULL;
  closure_evalvoid(C);
}

GEN
closure_callgen1(GEN C, GEN x)
{
  long i, ar = closure_arity(C);
  gel(st,sp++) = x;
  for(i=2; i<= ar; i++) gel(st,sp++) = NULL;
  return closure_returnupto(C);
}

GEN
closure_callgen1prec(GEN C, GEN x, long prec)
{
  GEN z;
  long i, ar = closure_arity(C);
  gel(st,sp++) = x;
  for(i=2; i<= ar; i++) gel(st,sp++) = NULL;
  push_localprec(prec);
  z = closure_returnupto(C);
  pop_localprec();
  return z;
}

GEN
closure_callgen2(GEN C, GEN x, GEN y)
{
  long i, ar = closure_arity(C);
  st_alloc(ar);
  gel(st,sp++) = x;
  gel(st,sp++) = y;
  for(i=3; i<=ar; i++) gel(st,sp++) = NULL;
  return closure_returnupto(C);
}

GEN
closure_callgenvec(GEN C, GEN args)
{
  long i, l = lg(args)-1, ar = closure_arity(C);
  st_alloc(ar);
  if (l > ar)
    pari_err(e_MISC,"too many parameters in user-defined function call");
  if (closure_is_variadic(C) && l==ar && typ(gel(args,l))!=t_VEC)
    pari_err_TYPE("call", gel(args,l));
  for (i = 1; i <= l;  i++) gel(st,sp++) = gel(args,i);
  for(      ; i <= ar; i++) gel(st,sp++) = NULL;
  return closure_returnupto(C);
}

GEN
closure_callgenvecprec(GEN C, GEN args, long prec)
{
  GEN z;
  push_localprec(prec);
  z = closure_callgenvec(C, args);
  pop_localprec();
  return z;
}

GEN
closure_callgenall(GEN C, long n, ...)
{
  va_list ap;
  long i, ar = closure_arity(C);
  va_start(ap,n);
  if (n > ar)
    pari_err(e_MISC,"too many parameters in user-defined function call");
  st_alloc(ar);
  for (i = 1; i <=n;  i++) gel(st,sp++) = va_arg(ap, GEN);
  for(      ; i <=ar; i++) gel(st,sp++) = NULL;
  va_end(ap);
  return closure_returnupto(C);
}

GEN
gp_eval(void *E, GEN x)
{
  GEN code = (GEN)E;
  set_lex(-1,x);
  return closure_evalnobrk(code);
}

GEN
gp_evalupto(void *E, GEN x)
{
  pari_sp av = avma;
  return copyupto(gp_eval(E,x), (GEN)av);
}

GEN
gp_evalprec(void *E, GEN x, long prec)
{
  GEN z;
  push_localprec(prec);
  z = gp_eval(E, x);
  pop_localprec();
  return z;
}

long
gp_evalbool(void *E, GEN x)
{
  pari_sp av = avma;
  long res  = !gequal0(gp_eval(E,x));
  avma = av; return res;
}

long
gp_evalvoid(void *E, GEN x)
{
  GEN code = (GEN)E;
  set_lex(-1,x);
  closure_evalvoid(code);
  return loop_break();
}

GEN
gp_call(void *E, GEN x)
{
  GEN code = (GEN)E;
  return closure_callgen1(code, x);
}

GEN
gp_callprec(void *E, GEN x, long prec)
{
  GEN code = (GEN)E;
  return closure_callgen1prec(code, x, prec);
}

GEN
gp_call2(void *E, GEN x, GEN y)
{
  GEN code = (GEN)E;
  return closure_callgen2(code, x, y);
}

long
gp_callbool(void *E, GEN x)
{
  pari_sp av = avma;
  GEN code = (GEN)E;
  long res  = !gequal0(closure_callgen1(code, x));
  avma = av; return res;
}

long
gp_callvoid(void *E, GEN x)
{
  GEN code = (GEN)E;
  closure_callvoid1(code, x);
  return loop_break();
}

INLINE const char *
disassemble_cast(long mode)
{
  switch (mode)
  {
  case Gsmall:
    return "small";
  case Ggen:
    return "gen";
  case Gvar:
    return "var";
  case Gvoid:
    return "void";
  default:
    return "unknown";
  }
}

void
closure_disassemble(GEN C)
{
  const char * code;
  GEN oper;
  long i;
  if (typ(C)!=t_CLOSURE) pari_err_TYPE("disassemble",C);
  code=closure_codestr(C);
  oper=closure_get_oper(C);
  for(i=1;i<lg(oper);i++)
  {
    op_code opcode=(op_code) code[i];
    long operand=oper[i];
    pari_printf("%05ld\t",i);
    switch(opcode)
    {
    case OCpushlong:
      pari_printf("pushlong\t%ld\n",operand);
      break;
    case OCpushgnil:
      pari_printf("pushgnil\n");
      break;
    case OCpushgen:
      pari_printf("pushgen\t\t%ld\n",operand);
      break;
    case OCpushreal:
      pari_printf("pushreal\t%ld\n",operand);
      break;
    case OCpushstoi:
      pari_printf("pushstoi\t%ld\n",operand);
      break;
    case OCpushvar:
      {
        entree *ep = (entree *)operand;
        pari_printf("pushvar\t%s\n",ep->name);
        break;
      }
    case OCpushdyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("pushdyn\t\t%s\n",ep->name);
        break;
      }
    case OCpushlex:
      pari_printf("pushlex\t\t%ld\n",operand);
      break;
    case OCstoredyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("storedyn\t%s\n",ep->name);
        break;
      }
    case OCstorelex:
      pari_printf("storelex\t%ld\n",operand);
      break;
    case OCstoreptr:
      pari_printf("storeptr\n");
      break;
    case OCsimpleptrdyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("simpleptrdyn\t%s\n",ep->name);
        break;
      }
    case OCsimpleptrlex:
      pari_printf("simpleptrlex\t%ld\n",operand);
      break;
    case OCnewptrdyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("newptrdyn\t%s\n",ep->name);
        break;
      }
    case OCnewptrlex:
      pari_printf("newptrlex\t%ld\n",operand);
      break;
    case OCpushptr:
      pari_printf("pushptr\n");
      break;
    case OCstackgen:
      pari_printf("stackgen\t%ld\n",operand);
      break;
    case OCendptr:
      pari_printf("endptr\t\t%ld\n",operand);
      break;
    case OCprecreal:
      pari_printf("precreal\n");
      break;
    case OCbitprecreal:
      pari_printf("bitprecreal\n");
      break;
    case OCprecdl:
      pari_printf("precdl\n");
      break;
    case OCstoi:
      pari_printf("stoi\n");
      break;
    case OCutoi:
      pari_printf("utoi\n");
      break;
    case OCitos:
      pari_printf("itos\t\t%ld\n",operand);
      break;
    case OCitou:
      pari_printf("itou\t\t%ld\n",operand);
      break;
    case OCtostr:
      pari_printf("tostr\t\t%ld\n",operand);
      break;
    case OCvarn:
      pari_printf("varn\t\t%ld\n",operand);
      break;
    case OCcopy:
      pari_printf("copy\n");
      break;
    case OCcopyifclone:
      pari_printf("copyifclone\n");
      break;
    case OCcompo1:
      pari_printf("compo1\t\t%s\n",disassemble_cast(operand));
      break;
    case OCcompo1ptr:
      pari_printf("compo1ptr\n");
      break;
    case OCcompo2:
      pari_printf("compo2\t\t%s\n",disassemble_cast(operand));
      break;
    case OCcompo2ptr:
      pari_printf("compo2ptr\n");
      break;
    case OCcompoC:
      pari_printf("compoC\n");
      break;
    case OCcompoCptr:
      pari_printf("compoCptr\n");
      break;
    case OCcompoL:
      pari_printf("compoL\n");
      break;
    case OCcompoLptr:
      pari_printf("compoLptr\n");
      break;
    case OCcheckargs:
      pari_printf("checkargs\t0x%lx\n",operand);
      break;
    case OCcheckargs0:
      pari_printf("checkargs0\t0x%lx\n",operand);
      break;
    case OCcheckuserargs:
      pari_printf("checkuserargs\t%ld\n",operand);
      break;
    case OCdefaultlong:
      pari_printf("defaultlong\t%ld\n",operand);
      break;
    case OCdefaultulong:
      pari_printf("defaultulong\t%ld\n",operand);
      break;
    case OCdefaultgen:
      pari_printf("defaultgen\t%ld\n",operand);
      break;
    case OCgetargs:
      pari_printf("getargs\t\t%ld\n",operand);
      break;
    case OCdefaultarg:
      pari_printf("defaultarg\t%ld\n",operand);
      break;
    case OClocalvar:
      {
        entree *ep = (entree *)operand;
        pari_printf("localvar\t%s\n",ep->name);
        break;
      }
    case OClocalvar0:
      {
        entree *ep = (entree *)operand;
        pari_printf("localvar0\t%s\n",ep->name);
        break;
      }
    case OCcallgen:
      {
        entree *ep = (entree *)operand;
        pari_printf("callgen\t\t%s\n",ep->name);
        break;
      }
    case OCcallgen2:
      {
        entree *ep = (entree *)operand;
        pari_printf("callgen2\t%s\n",ep->name);
        break;
      }
    case OCcalllong:
      {
        entree *ep = (entree *)operand;
        pari_printf("calllong\t%s\n",ep->name);
        break;
      }
    case OCcallint:
      {
        entree *ep = (entree *)operand;
        pari_printf("callint\t\t%s\n",ep->name);
        break;
      }
    case OCcallvoid:
      {
        entree *ep = (entree *)operand;
        pari_printf("callvoid\t%s\n",ep->name);
        break;
      }
    case OCcalluser:
      pari_printf("calluser\t%ld\n",operand);
      break;
    case OCvec:
      pari_printf("vec\t\t%ld\n",operand);
      break;
    case OCcol:
      pari_printf("col\t\t%ld\n",operand);
      break;
    case OCmat:
      pari_printf("mat\t\t%ld\n",operand);
      break;
    case OCnewframe:
      pari_printf("newframe\t%ld\n",operand);
      break;
    case OCsaveframe:
      pari_printf("saveframe\t%ld\n", operand);
      break;
    case OCpop:
      pari_printf("pop\t\t%ld\n",operand);
      break;
    case OCdup:
      pari_printf("dup\t\t%ld\n",operand);
      break;
    case OCavma:
      pari_printf("avma\n",operand);
      break;
    case OCgerepile:
      pari_printf("gerepile\n",operand);
      break;
    case OCcowvardyn:
      {
        entree *ep = (entree *)operand;
        pari_printf("cowvardyn\t%s\n",ep->name);
        break;
      }
    case OCcowvarlex:
      pari_printf("cowvarlex\t%ld\n",operand);
      break;
    }
  }
}

static int
opcode_need_relink(op_code opcode)
{
  switch(opcode)
  {
  case OCpushlong:
  case OCpushgen:
  case OCpushgnil:
  case OCpushreal:
  case OCpushstoi:
  case OCpushlex:
  case OCstorelex:
  case OCstoreptr:
  case OCsimpleptrlex:
  case OCnewptrlex:
  case OCpushptr:
  case OCstackgen:
  case OCendptr:
  case OCprecreal:
  case OCbitprecreal:
  case OCprecdl:
  case OCstoi:
  case OCutoi:
  case OCitos:
  case OCitou:
  case OCtostr:
  case OCvarn:
  case OCcopy:
  case OCcopyifclone:
  case OCcompo1:
  case OCcompo1ptr:
  case OCcompo2:
  case OCcompo2ptr:
  case OCcompoC:
  case OCcompoCptr:
  case OCcompoL:
  case OCcompoLptr:
  case OCcheckargs:
  case OCcheckargs0:
  case OCcheckuserargs:
  case OCgetargs:
  case OCdefaultarg:
  case OCdefaultgen:
  case OCdefaultlong:
  case OCdefaultulong:
  case OCcalluser:
  case OCvec:
  case OCcol:
  case OCmat:
  case OCnewframe:
  case OCsaveframe:
  case OCdup:
  case OCpop:
  case OCavma:
  case OCgerepile:
  case OCcowvarlex:
    break;
  case OCpushvar:
  case OCpushdyn:
  case OCstoredyn:
  case OCsimpleptrdyn:
  case OCnewptrdyn:
  case OClocalvar:
  case OClocalvar0:
  case OCcallgen:
  case OCcallgen2:
  case OCcalllong:
  case OCcallint:
  case OCcallvoid:
  case OCcowvardyn:
    return 1;
  }
  return 0;
}

static void
closure_relink(GEN C, hashtable *table)
{
  const char *code = closure_codestr(C);
  GEN oper = closure_get_oper(C);
  GEN fram = gel(closure_get_dbg(C),3);
  long i, j;
  for(i=1;i<lg(oper);i++)
    if (oper[i] && opcode_need_relink((op_code)code[i]))
      oper[i] = (long) hash_search(table,(void*) oper[i])->val;
  for (i=1;i<lg(fram);i++)
    for (j=1;j<lg(gel(fram,i));j++)
      if (mael(fram,i,j))
        mael(fram,i,j) = (long) hash_search(table,(void*) mael(fram,i,j))->val;
}

void
gen_relink(GEN x, hashtable *table)
{
  long i, lx, tx = typ(x);
  switch(tx)
  {
    case t_CLOSURE:
      closure_relink(x, table);
      gen_relink(closure_get_data(x), table);
      if (lg(x)==8) gen_relink(closure_get_frame(x), table);
      break;
    case t_LIST:
      if (list_data(x)) gen_relink(list_data(x), table);
      break;
    case t_VEC: case t_COL: case t_MAT: case t_ERROR:
      lx = lg(x);
      for (i=lontyp[tx]; i<lx; i++) gen_relink(gel(x,i), table);
  }
}

static void
closure_unlink(GEN C)
{
  const char *code = closure_codestr(C);
  GEN oper = closure_get_oper(C);
  GEN fram = gel(closure_get_dbg(C),3);
  long i, j;
  for(i=1;i<lg(oper);i++)
    if (oper[i] && opcode_need_relink((op_code) code[i]))
    {
      long n = pari_stack_new(&s_relocs);
      relocs[n] = (entree *) oper[i];
    }
  for (i=1;i<lg(fram);i++)
    for (j=1;j<lg(gel(fram,i));j++)
      if (mael(fram,i,j))
      {
        long n = pari_stack_new(&s_relocs);
        relocs[n] = (entree *) mael(fram,i,j);
      }
}

static void
gen_unlink(GEN x)
{
  long i, lx, tx = typ(x);
  switch(tx)
  {
    case t_CLOSURE:
      closure_unlink(x);
      gen_unlink(closure_get_data(x));
      if (lg(x)==8) gen_unlink(closure_get_frame(x));
      break;
    case t_LIST:
      if (list_data(x)) gen_unlink(list_data(x));
      break;
    case t_VEC: case t_COL: case t_MAT: case t_ERROR:
      lx = lg(x);
      for (i = lontyp[tx]; i<lx; i++) gen_unlink(gel(x,i));
  }
}

GEN
copybin_unlink(GEN C)
{
  long i, l , n, nold = s_relocs.n;
  GEN v, w, V, res;
  if (C)
    gen_unlink(C);
  else
  { /* contents of all variables */
    long v, maxv = pari_var_next();
    for (v=0; v<maxv; v++)
    {
      entree *ep = varentries[v];
      if (!ep || !ep->value) continue;
      gen_unlink((GEN)ep->value);
    }
  }
  n = s_relocs.n-nold;
  v = cgetg(n+1, t_VECSMALL);
  for(i=0; i<n; i++)
    v[i+1] = (long) relocs[i];
  s_relocs.n = nold;
  w = vecsmall_uniq(v); l = lg(w);
  res = cgetg(3,t_VEC);
  V = cgetg(l, t_VEC);
  for(i=1; i<l; i++)
  {
    entree *ep = (entree*) w[i];
    gel(V,i) = strtoGENstr(ep->name);
  }
  gel(res,1) = vecsmall_copy(w);
  gel(res,2) = V;
  return res;
}

/* e = t_VECSMALL of entree *ep [ addresses ],
 * names = t_VEC of strtoGENstr(ep.names),
 * Return hashtable : ep => is_entry(ep.name) */
hashtable *
hash_from_link(GEN e, GEN names, int use_stack)
{
  long i, l = lg(e);
  hashtable *h = hash_create_ulong(l-1, use_stack);
  if (lg(names) != l) pari_err_DIM("hash_from_link");
  for (i = 1; i < l; i++)
  {
    char *s = GSTR(gel(names,i));
    hash_insert(h, (void*)e[i], (void*)fetch_entry(s));
  }
  return h;
}

void
bincopy_relink(GEN C, GEN V)
{
  pari_sp av = avma;
  hashtable *table = hash_from_link(gel(V,1),gel(V,2),1);
  gen_relink(C, table);
  avma = av;
}
