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
#include "tree.h"
#include "opcode.h"

#define tree pari_tree

enum COflags {COsafelex=1, COsafedyn=2};

/***************************************************************************
 **                                                                       **
 **                           String constant expansion                   **
 **                                                                       **
 ***************************************************************************/

static char *
translate(const char **src, char *s)
{
  const char *t = *src;
  while (*t)
  {
    while (*t == '\\')
    {
      switch(*++t)
      {
        case 'e':  *s='\033'; break; /* escape */
        case 'n':  *s='\n'; break;
        case 't':  *s='\t'; break;
        default:   *s=*t; if (!*t) { *src=s; return NULL; }
      }
      t++; s++;
    }
    if (*t == '"')
    {
      if (t[1] != '"') break;
      t += 2; continue;
    }
    *s++ = *t++;
  }
  *s=0; *src=t; return s;
}

static void
matchQ(const char *s, char *entry)
{
  if (*s != '"')
    pari_err(e_SYNTAX,"expected character: '\"' instead of",s,entry);
}

/*  Read a "string" from src. Format then copy it, starting at s. Return
 *  pointer to char following the end of the input string */
char *
pari_translate_string(const char *src, char *s, char *entry)
{
  matchQ(src, entry); src++; s = translate(&src, s);
  if (!s) pari_err(e_SYNTAX,"run-away string",src,entry);
  matchQ(src, entry); return (char*)src+1;
}

static GEN
strntoGENexp(const char *str, long len)
{
  GEN z = cgetg(1+nchar2nlong(len-1), t_STR);
  const char *t = str+1;
  if (!translate(&t, GSTR(z))) compile_err("run-away string",str);
  return z;
}

/***************************************************************************
 **                                                                       **
 **                           Byte-code compiler                          **
 **                                                                       **
 ***************************************************************************/

typedef enum {Llocal, Lmy} Ltype;

struct vars_s
{
  Ltype type; /*Only Llocal and Lmy are allowed */
  int inl;
  entree *ep;
};

struct frame_s
{
  long pc;
  GEN frame;
};

static THREAD pari_stack s_opcode, s_operand, s_data, s_lvar;
static THREAD pari_stack s_dbginfo, s_frame;
static THREAD char *opcode;
static THREAD long *operand;
static THREAD GEN *data;
static THREAD long offset;
static THREAD struct vars_s *localvars;
static THREAD const char **dbginfo, *dbgstart;
static THREAD struct frame_s *frames;

void
pari_init_compiler(void)
{
  pari_stack_init(&s_opcode,sizeof(*opcode),(void **)&opcode);
  pari_stack_init(&s_operand,sizeof(*operand),(void **)&operand);
  pari_stack_init(&s_data,sizeof(*data),(void **)&data);
  pari_stack_init(&s_lvar,sizeof(*localvars),(void **)&localvars);
  pari_stack_init(&s_dbginfo,sizeof(*dbginfo),(void **)&dbginfo);
  pari_stack_init(&s_frame,sizeof(*frames),(void **)&frames);
  offset=-1;
}
void
pari_close_compiler(void)
{
  pari_stack_delete(&s_opcode);
  pari_stack_delete(&s_operand);
  pari_stack_delete(&s_data);
  pari_stack_delete(&s_lvar);
  pari_stack_delete(&s_dbginfo);
  pari_stack_delete(&s_frame);
}

struct codepos
{
  long opcode, data, localvars, frames;
  long offset;
  const char *dbgstart;
};

static void
getcodepos(struct codepos *pos)
{
  pos->opcode=s_opcode.n;
  pos->data=s_data.n;
  pos->offset=offset;
  pos->localvars=s_lvar.n;
  pos->dbgstart=dbgstart;
  pos->frames=s_frame.n;
  offset=s_data.n-1;
}

void
compilestate_reset(void)
{
  s_opcode.n=0;
  s_operand.n=0;
  s_dbginfo.n=0;
  s_data.n=0;
  s_lvar.n=0;
  s_frame.n=0;
  offset=-1;
  dbgstart=NULL;
}

void
compilestate_save(struct pari_compilestate *comp)
{
  comp->opcode=s_opcode.n;
  comp->operand=s_operand.n;
  comp->data=s_data.n;
  comp->offset=offset;
  comp->localvars=s_lvar.n;
  comp->dbgstart=dbgstart;
  comp->dbginfo=s_dbginfo.n;
  comp->frames=s_frame.n;
}

void
compilestate_restore(struct pari_compilestate *comp)
{
  s_opcode.n=comp->opcode;
  s_operand.n=comp->operand;
  s_data.n=comp->data;
  offset=comp->offset;
  s_lvar.n=comp->localvars;
  dbgstart=comp->dbgstart;
  s_dbginfo.n=comp->dbginfo;
  s_frame.n=comp->frames;
}

static GEN
getfunction(const struct codepos *pos, long arity, long nbmvar, GEN text, long gap)
{
  long lop =s_opcode.n+1-pos->opcode;
  long ldat=s_data.n+1-pos->data;
  long lfram=s_frame.n+1-pos->frames;
  GEN cl=cgetg(nbmvar?8:(text?7:6),t_CLOSURE);
  GEN frpc, fram, dbg;
  char *s;
  long i;
  cl[1] = arity;
  gel(cl,2) = cgetg(nchar2nlong(lop)+1, t_STR);
  gel(cl,3) = cgetg(lop,  t_VECSMALL);
  gel(cl,4) = cgetg(ldat, t_VEC);
  dbg = cgetg(lop,  t_VECSMALL);
  frpc = cgetg(lfram,  t_VECSMALL);
  fram = cgetg(lfram,  t_VEC);
  gel(cl,5) = mkvec3(dbg, frpc, fram);
  if (text) gel(cl,6) = text;
  if (nbmvar) gel(cl,7) = zerovec(nbmvar);
  s=GSTR(gel(cl,2))-1;
  for(i=1;i<lop;i++)
  {
    s[i] = opcode[i+pos->opcode-1];
    mael(cl, 3, i) = operand[i+pos->opcode-1];
    dbg[i] = dbginfo[i+pos->opcode-1]-dbgstart;
    if (dbg[i]<0) dbg[i]+=gap;
  }
  s[i]=0;
  s_opcode.n=pos->opcode;
  s_operand.n=pos->opcode;
  s_dbginfo.n=pos->opcode;
  for(i=1;i<ldat;i++)
    if(data[i+pos->data-1])
    {
      gmael(cl, 4, i) = gcopy(data[i+pos->data-1]);
      gunclone(data[i+pos->data-1]);
    }
  s_data.n=pos->data;
  while (s_lvar.n>pos->localvars && !localvars[s_lvar.n-1].inl)
    s_lvar.n--;
  for(i=1;i<lfram;i++)
  {
    long j=i+pos->frames-1;
    frpc[i] = frames[j].pc-pos->opcode+1;
    gel(fram, i) = gcopy(frames[j].frame);
    gunclone(frames[j].frame);
  }
  s_frame.n=pos->frames;
  offset=pos->offset;
  dbgstart=pos->dbgstart;
  return cl;
}

static GEN
getclosure(struct codepos *pos)
{
  return getfunction(pos,0,0,NULL,0);
}

static void
op_push_loc(op_code o, long x, const char *loc)
{
  long n=pari_stack_new(&s_opcode);
  long m=pari_stack_new(&s_operand);
  long d=pari_stack_new(&s_dbginfo);
  opcode[n]=o;
  operand[m]=x;
  dbginfo[d]=loc;
}

static void
op_push(op_code o, long x, long n)
{
  op_push_loc(o,x,tree[n].str);
}

static void
op_insert_loc(long k, op_code o, long x, const char *loc)
{
  long i;
  long n=pari_stack_new(&s_opcode);
  (void) pari_stack_new(&s_operand);
  (void) pari_stack_new(&s_dbginfo);
  for (i=n-1; i>=k; i--)
  {
    opcode[i+1] = opcode[i];
    operand[i+1]= operand[i];
    dbginfo[i+1]= dbginfo[i];
  }
  opcode[k]  = o;
  operand[k] = x;
  dbginfo[k] = loc;
}

static long
data_push(GEN x)
{
  long n=pari_stack_new(&s_data);
  data[n] = x?gclone(x):x;
  return n-offset;
}

static void
var_push(entree *ep, Ltype type)
{
  long n=pari_stack_new(&s_lvar);
  localvars[n].ep   = ep;
  localvars[n].inl  = 0;
  localvars[n].type = type;
}

static void
frame_push(GEN x)
{
  long n=pari_stack_new(&s_frame);
  frames[n].pc = s_opcode.n-1;
  frames[n].frame = gclone(x);
}

static GEN
pack_localvars(void)
{
  GEN pack=cgetg(3,t_VEC);
  long i,l=s_lvar.n;
  GEN t=cgetg(1+l,t_VECSMALL);
  GEN e=cgetg(1+l,t_VECSMALL);
  gel(pack,1)=t;
  gel(pack,2)=e;
  for(i=1;i<=l;i++)
  {
    t[i]=localvars[i-1].type;
    e[i]=(long)localvars[i-1].ep;
  }
  return pack;
}

void
push_frame(GEN C, long lpc, long dummy)
{
  const char *code=closure_codestr(C);
  GEN oper=closure_get_oper(C);
  GEN dbg=closure_get_dbg(C);
  GEN frpc=gel(dbg,2);
  GEN fram=gel(dbg,3);
  long pc, j=1, lfr = lg(frpc);
  if (lpc==-1)
  {
    long k;
    GEN e = gel(fram, 1);
    for(k=1; k<lg(e); k++)
      var_push(dummy?NULL:(entree*)e[k], Lmy);
    return;
  }
  if (lg(C)<8) while (j<lfr && frpc[j]==0) j++;
  for(pc=0; pc<lpc; pc++) /* do not assume lpc was completed */
  {
    if (pc>0 && (code[pc]==OClocalvar || code[pc]==OClocalvar0))
      var_push((entree*)oper[pc],Llocal);
    if (j<lfr && pc==frpc[j])
    {
      long k;
      GEN e = gel(fram,j);
      for(k=1; k<lg(e); k++)
        var_push(dummy?NULL:(entree*)e[k], Lmy);
      j++;
    }
  }
}

void
debug_context(void)
{
  long i;
  for(i=0;i<s_lvar.n;i++)
  {
    entree *ep = localvars[i].ep;
    Ltype type = localvars[i].type;
    err_printf("%ld: %s: %s\n",i,(type==Lmy?"my":"local"),(ep?ep->name:"NULL"));
  }
}

GEN
localvars_read_str(const char *x, GEN pack)
{
  GEN code;
  long l=0;
  if (pack)
  {
    GEN t=gel(pack,1);
    GEN e=gel(pack,2);
    long i;
    l=lg(t)-1;
    for(i=1;i<=l;i++)
      var_push((entree*)e[i],(Ltype)t[i]);
  }
  code = compile_str(x);
  s_lvar.n -= l;
  return closure_evalres(code);
}

long
localvars_find(GEN pack, entree *ep)
{
  GEN t=gel(pack,1);
  GEN e=gel(pack,2);
  long i;
  long vn=0;
  for(i=lg(e)-1;i>=1;i--)
  {
    if(t[i]==Lmy)
      vn--;
    if(e[i]==(long)ep)
      return t[i]==Lmy?vn:0;
  }
  return 0;
}

/*
 Flags for copy optimisation:
 -- Freturn: The result will be returned.
 -- FLsurvive: The result must survive the closure.
 -- FLnocopy: The result will never be updated nor part of a user variable.
 -- FLnocopylex: The result will never be updated nor part of dynamic variable.
*/
enum FLflag {FLreturn=1, FLsurvive=2, FLnocopy=4, FLnocopylex=8};

static void
addcopy(long n, long mode, long flag, long mask)
{
  if (mode==Ggen && !(flag&mask))
  {
    op_push(OCcopy,0,n);
    if (!(flag&FLsurvive) && DEBUGLEVEL)
      pari_warn(warner,"compiler generates copy for `%.*s'",
                       tree[n].len,tree[n].str);
  }
}

static void compilenode(long n, int mode, long flag);

typedef enum {PPend,PPstd,PPdefault,PPdefaultmulti,PPstar,PPauto} PPproto;

static PPproto
parseproto(char const **q, char *c, const char *str)
{
  char  const *p=*q;
  long i;
  switch(*p)
  {
  case 0:
  case '\n':
    return PPend;
  case 'D':
    switch(p[1])
    {
    case 0:
      compile_err("function has incomplete prototype",str);
    case 'G':
    case '&':
    case 'W':
    case 'V':
    case 'I':
    case 'E':
    case 'J':
    case 'n':
    case 'P':
    case 'r':
    case 's':
      *c=p[1];
      *q=p+2;
      return PPdefault;
    default:
      for(i=0;*p && i<2;p++) i+=*p==',';
      if (i<2)
        compile_err("function has incomplete prototype",str);
      *c=p[-2];
      *q=p;
      return PPdefaultmulti;
    }
    break;
  case 'C':
  case 'p':
  case 'b':
  case 'P':
  case 'f':
    *c=*p;
    *q=p+1;
    return PPauto;
  case '&':
    *c='*';
    *q=p+1;
    return PPstd;
  case 'V':
    if (p[1]=='=')
    {
      if (p[2]!='G')
        compile_err("function prototype is not supported",str);
      *c='=';
      p+=2;
    }
    else
      *c=*p;
    *q=p+1;
    return PPstd;
  case 'E':
  case 's':
    if (p[1]=='*')
    {
      *c=*p++;
      *q=p+1;
      return PPstar;
    }
    /*fall through*/
  }
  *c=*p;
  *q=p+1;
  return PPstd;
}

static long
detag(long n)
{
  while (tree[n].f==Ftag)
    n=tree[n].x;
  return n;
}

/* return type for GP functions */
static op_code
get_ret_type(const char **p, long arity, Gtype *t, long *flag)
{
  *flag = 0;
  if (**p == 'v') { (*p)++; *t=Gvoid; return OCcallvoid; }
  else if (**p == 'i') { (*p)++; *t=Gsmall;  return OCcallint; }
  else if (**p == 'l') { (*p)++; *t=Gsmall;  return OCcalllong; }
  else if (**p == 'u') { (*p)++; *t=Gusmall; return OCcalllong; }
  else if (**p == 'm') { (*p)++; *flag = FLnocopy; }
  *t=Ggen; return arity==2?OCcallgen2:OCcallgen;
}

/*supported types:
 * type: Gusmall, Gsmall, Ggen, Gvoid, Gvec, Gclosure
 * mode: Gusmall, Gsmall, Ggen, Gvar, Gvoid
 */
static void
compilecast_loc(int type, int mode, const char *loc)
{
  if (type==mode) return;
  switch (mode)
  {
  case Gusmall:
    if (type==Ggen)        op_push_loc(OCitou,-1,loc);
    else if (type==Gvoid)  op_push_loc(OCpushlong,0,loc);
    else if (type!=Gsmall)
      compile_err("this should be a small integer >=0",loc);
    break;
  case Gsmall:
    if (type==Ggen)        op_push_loc(OCitos,-1,loc);
    else if (type==Gvoid)  op_push_loc(OCpushlong,0,loc);
    else if (type!=Gusmall)
      compile_err("this should be a small integer",loc);
    break;
  case Ggen:
    if (type==Gsmall)      op_push_loc(OCstoi,0,loc);
    else if (type==Gusmall)op_push_loc(OCutoi,0,loc);
    else if (type==Gvoid)  op_push_loc(OCpushgnil,0,loc);
    break;
  case Gvoid:
    op_push_loc(OCpop, 1,loc);
    break;
  case Gvar:
    if (type==Ggen)        op_push_loc(OCvarn,-1,loc);
    else compile_varerr(loc);
     break;
  default:
    pari_err_BUG("compilecast [unknown type]");
  }
}

static void
compilecast(long n, int type, int mode) { compilecast_loc(type, mode, tree[n].str); }

static entree *
fetch_member_raw(const char *s, long len)
{
  pari_sp av = avma;
  char *t = stack_malloc(len+2);
  entree *ep;
  t[0] = '_'; strncpy(t+1, s, len); t[++len] = 0; /* prepend '_' */
  ep = fetch_entry_raw(t, len);
  avma = av; return ep;
}
static entree *
getfunc(long n)
{
  long x=tree[n].x;
  if (tree[x].x==CSTmember) /* str-1 points to '.' */
    return do_alias(fetch_member_raw(tree[x].str - 1, tree[x].len + 1));
  else
    return do_alias(fetch_entry_raw(tree[x].str, tree[x].len));
}

static entree *
getentry(long n)
{
  n = detag(n);
  if (tree[n].f!=Fentry)
  {
    if (tree[n].f==Fseq)
      compile_err("unexpected character: ';'", tree[tree[n].y].str-1);
    compile_varerr(tree[n].str);
  }
  return getfunc(n);
}

/* match Fentry that are not actually EpSTATIC functions called without parens*/
static entree *
getvar(long n)
{
  entree *ep = getentry(n);
  if (EpSTATIC(do_alias(ep)))
    compile_varerr(tree[n].str);
  return ep;
}

static long
getmvar(entree *ep)
{
  long i;
  long vn=0;
  for(i=s_lvar.n-1;i>=0;i--)
  {
    if(localvars[i].type==Lmy)
      vn--;
    if(localvars[i].ep==ep)
      return localvars[i].type==Lmy?vn:0;
  }
  return 0;
}

static long
ctxmvar(void)
{
  pari_sp av=avma;
  long i, n=0;
  GEN ctx;
  for(i=s_lvar.n-1;i>=0;i--)
    if(localvars[i].type==Lmy)
      n++;
  if (n==0) return 0;
  ctx = cgetg(n+1,t_VECSMALL);
  for(n=0, i=0; i<s_lvar.n; i++)
    if(localvars[i].type==Lmy)
      ctx[++n]=(long)localvars[i].ep;
  frame_push(ctx);
  avma=av; return n;
}

INLINE int
is_func_named(entree *ep, const char *s)
{
  return !strcmp(ep->name, s);
}

INLINE int
is_node_zero(long n)
{
  n = detag(n);
  return (tree[n].f==Fsmall && tree[n].x==0);
}

static void
str_defproto(const char *p, const char *q, const char *loc)
{
  long len = p-4-q;
  if (q[1]!='"' || q[len]!='"')
    compile_err("default argument must be a string",loc);
  op_push_loc(OCpushgen,data_push(strntoGENexp(q+1,len)),loc);
}

static long
countlisttogen(long n, Ffunc f)
{
  long x,i;
  if (n==-1 || tree[n].f==Fnoarg) return 0;
  for(x=n, i=0; tree[x].f==f ;x=tree[x].x, i++);
  return i+1;
}

static GEN
listtogen(long n, Ffunc f)
{
  long x,i,nb = countlisttogen(n, f);
  GEN z=cgetg(nb+1, t_VECSMALL);
  if (nb)
  {
    for (x=n, i = nb-1; i>0; z[i+1]=tree[x].y, x=tree[x].x, i--);
    z[1]=x;
  }
  return z;
}

static long
first_safe_arg(GEN arg, long mask)
{
  long lnc, l=lg(arg);
  for (lnc=l-1; lnc>0 && (tree[arg[lnc]].flags&mask)==mask; lnc--);
  return lnc;
}

static void
checkdups(GEN arg, GEN vep)
{
  long l=vecsmall_duplicate(vep);
  if (l!=0) compile_err("variable declared twice",tree[arg[l]].str);
}

enum {MAT_range,MAT_std,MAT_line,MAT_column,VEC_std};

static int
matindex_type(long n)
{
  long x = tree[n].x, y = tree[n].y;
  long fxx = tree[tree[x].x].f, fxy = tree[tree[x].y].f;
  if (y==-1)
  {
    if (fxy!=Fnorange) return MAT_range;
    if (fxx==Fnorange) compile_err("missing index",tree[n].str);
    return VEC_std;
  }
  else
  {
    long fyx = tree[tree[y].x].f, fyy = tree[tree[y].y].f;
    if (fxy!=Fnorange || fyy!=Fnorange) return MAT_range;
    if (fxx==Fnorange && fyx==Fnorange)
      compile_err("missing index",tree[n].str);
    if (fxx==Fnorange) return MAT_column;
    if (fyx==Fnorange) return MAT_line;
    return MAT_std;
  }
}

static entree *
getlvalue(long n)
{
  while ((tree[n].f==Fmatcoeff && matindex_type(tree[n].y)!=MAT_range) || tree[n].f==Ftag)
    n=tree[n].x;
  return getvar(n);
}

INLINE void
compilestore(long vn, entree *ep, long n)
{
  if (vn)
    op_push(OCstorelex,vn,n);
  else
    op_push(OCstoredyn,(long)ep,n);
}

INLINE void
compilenewptr(long vn, entree *ep, long n)
{
  if (vn)
    op_push(OCnewptrlex,vn,n);
  else
    op_push(OCnewptrdyn,(long)ep,n);
}

static void
compilelvalue(long n)
{
  n = detag(n);
  if (tree[n].f==Fentry)
    return;
  else
  {
    long x = tree[n].x, y = tree[n].y;
    long yx = tree[y].x, yy = tree[y].y;
    long m = matindex_type(y);
    if (m == MAT_range)
      compile_err("not an lvalue",tree[n].str);
    if (m == VEC_std && tree[x].f==Fmatcoeff)
    {
      int mx = matindex_type(tree[x].y);
      if (mx==MAT_line)
      {
        int xy = tree[x].y, xyx = tree[xy].x;
        compilelvalue(tree[x].x);
        compilenode(tree[xyx].x,Gsmall,0);
        compilenode(tree[yx].x,Gsmall,0);
        op_push(OCcompo2ptr,0,y);
        return;
      }
    }
    compilelvalue(x);
    switch(m)
    {
    case VEC_std:
      compilenode(tree[yx].x,Gsmall,0);
      op_push(OCcompo1ptr,0,y);
      break;
    case MAT_std:
      compilenode(tree[yx].x,Gsmall,0);
      compilenode(tree[yy].x,Gsmall,0);
      op_push(OCcompo2ptr,0,y);
      break;
    case MAT_line:
      compilenode(tree[yx].x,Gsmall,0);
      op_push(OCcompoLptr,0,y);
      break;
    case MAT_column:
      compilenode(tree[yy].x,Gsmall,0);
      op_push(OCcompoCptr,0,y);
      break;
    }
  }
}

static void
compilematcoeff(long n, int mode)
{
  long x=tree[n].x, y=tree[n].y;
  long yx=tree[y].x, yy=tree[y].y;
  long m=matindex_type(y);
  compilenode(x,Ggen,FLnocopy);
  switch(m)
  {
  case VEC_std:
    compilenode(tree[yx].x,Gsmall,0);
    op_push(OCcompo1,mode,y);
    return;
  case MAT_std:
    compilenode(tree[yx].x,Gsmall,0);
    compilenode(tree[yy].x,Gsmall,0);
    op_push(OCcompo2,mode,y);
    return;
  case MAT_line:
    compilenode(tree[yx].x,Gsmall,0);
    op_push(OCcompoL,0,y);
    compilecast(n,Gvec,mode);
    return;
  case MAT_column:
    compilenode(tree[yy].x,Gsmall,0);
    op_push(OCcompoC,0,y);
    compilecast(n,Gvec,mode);
    return;
  case MAT_range:
    compilenode(tree[yx].x,Gsmall,0);
    compilenode(tree[yx].y,Gsmall,0);
    if (yy==-1)
      op_push(OCcallgen,(long)is_entry("_[_.._]"),n);
    else
    {
      compilenode(tree[yy].x,Gsmall,0);
      compilenode(tree[yy].y,Gsmall,0);
      op_push(OCcallgen,(long)is_entry("_[_.._,_.._]"),n);
    }
    compilecast(n,Gvec,mode);
    return;
  default:
    pari_err_BUG("compilematcoeff");
  }
}

static void
compilesmall(long n, long x, long mode)
{
  if (mode==Ggen)
    op_push(OCpushstoi, x, n);
  else
  {
    if (mode==Gusmall && x < 0)
      compile_err("this should be a small integer >=0",tree[n].str);
    op_push(OCpushlong, x, n);
    compilecast(n,Gsmall,mode);
  }
}

static void
compilevec(long n, long mode, op_code op)
{
  pari_sp ltop=avma;
  long x=tree[n].x;
  long i;
  GEN arg=listtogen(x,Fmatrixelts);
  long l=lg(arg);
  op_push(op,l,n);
  for (i=1;i<l;i++)
  {
    compilenode(arg[i],Ggen,FLsurvive);
    op_push(OCstackgen,i,n);
  }
  avma=ltop;
  op_push(OCpop,1,n);
  compilecast(n,Gvec,mode);
}

static void
compilemat(long n, long mode)
{
  pari_sp ltop=avma;
  long x=tree[n].x;
  long i,j;
  GEN line=listtogen(x,Fmatrixlines);
  long lglin = lg(line), lgcol=0;
  op_push(OCpushlong, lglin,n);
  if (lglin==1)
    op_push(OCmat,1,n);
  for(i=1;i<lglin;i++)
  {
    GEN col=listtogen(line[i],Fmatrixelts);
    long l=lg(col), k;
    if (i==1)
    {
      lgcol=l;
      op_push(OCmat,lgcol,n);
    }
    else if (l!=lgcol)
      compile_err("matrix must be rectangular",tree[line[i]].str);
    k=i;
    for(j=1;j<lgcol;j++)
    {
      k-=lglin;
      compilenode(col[j], Ggen, FLsurvive);
      op_push(OCstackgen,k,n);
    }
  }
  avma=ltop;
  op_push(OCpop,1,n);
  compilecast(n,Gvec,mode);
}


static GEN
cattovec(long n, long fnum)
{
  long x=n, y, i=0, nb;
  GEN stack;
  if (tree[n].f==Fnoarg) return cgetg(1,t_VECSMALL);
  while(1)
  {
    long xx=tree[x].x;
    long xy=tree[x].y;
    if (tree[x].f!=Ffunction || xx!=fnum) break;
    x=tree[xy].x;
    y=tree[xy].y;
    if (tree[y].f==Fnoarg)
      compile_err("unexpected character: ", tree[y].str);
    i++;
  }
  if (tree[x].f==Fnoarg)
    compile_err("unexpected character: ", tree[x].str);
  nb=i+1;
  stack=cgetg(nb+1,t_VECSMALL);
  for(x=n;i>0;i--)
  {
    long y=tree[x].y;
    x=tree[y].x;
    stack[i+1]=tree[y].y;
  }
  stack[1]=x;
  return stack;
}

static GEN
compilelambda(long n, long y, GEN vep, struct codepos *pos)
{
  long nbmvar, lev = vep ? lg(vep)-1 : 0;
  GEN text=cgetg(3,t_VEC);
  gel(text,1)=strtoGENstr(lev? ((entree*) vep[1])->name: "");
  gel(text,2)=strntoGENstr(tree[y].str,tree[y].len);
  dbgstart = tree[y].str;
  nbmvar=ctxmvar()-lev;
  if (lev) op_push(OCgetargs,lev,n);
  compilenode(y,Ggen,FLsurvive|FLreturn);
  return getfunction(pos,lev,nbmvar,text,2);
}

static void
compilecall(long n, int mode, entree *ep)
{
  pari_sp ltop=avma;
  long j;
  long x=tree[n].x;
  long y=tree[n].y;
  GEN arg=listtogen(y,Flistarg);
  long nb=lg(arg)-1;
  long lnc=first_safe_arg(arg, COsafelex|COsafedyn);
  long lnl=first_safe_arg(arg, COsafelex);
  long fl = lnl==0? (lnc==0? FLnocopy: FLnocopylex): 0;
  if (ep==NULL)
    compilenode(x, Ggen, fl);
  else
  {
    long vn=getmvar(ep);
    if (vn)
      op_push(OCpushlex,vn,n);
    else
      op_push(OCpushdyn,(long)ep,n);
  }
  for (j=1;j<=nb;j++)
  {
    long x = tree[arg[j]].x, f = tree[arg[j]].f;
    if (f==Fseq)
      compile_err("unexpected ';'", tree[x].str+tree[x].len);
    else if (f!=Fnoarg)
      compilenode(arg[j], Ggen,j>=lnl?FLnocopylex:0);
    else
      op_push(OCpushlong,0,n);
  }
  op_push(OCcalluser,nb,x);
  compilecast(n,Ggen,mode);
  avma=ltop;
}

static GEN
compilefuncinline(long n, long c, long a, long flag, long isif, long lev, long *ev)
{
  struct codepos pos;
  int type=c=='I'?Gvoid:Ggen;
  long rflag=c=='I'?0:FLsurvive;
  GEN vep = NULL;
  if (isif && (flag&FLreturn)) rflag|=FLreturn;
  getcodepos(&pos);
  if (lev)
  {
    long i;
    GEN varg=cgetg(lev+1,t_VECSMALL);
    vep=cgetg(lev+1,t_VECSMALL);
    for(i=0;i<lev;i++)
    {
      entree *ve;
      if (ev[i]<0)
        compile_err("missing variable name", tree[a].str-1);
      ve = getvar(ev[i]);
      vep[i+1]=(long)ve;
      varg[i+1]=ev[i];
      var_push(ve,Lmy);
    }
    checkdups(varg,vep);
    frame_push(vep);
  }
  if (c=='J')
    return compilelambda(n,a,vep,&pos);
  else if (tree[a].f==Fnoarg)
    compilecast(a,Gvoid,type);
  else
    compilenode(a,type,rflag);
  return getclosure(&pos);
}

static long
countvar(GEN arg)
{
  long i, l = lg(arg);
  long n = l-1;
  for(i=1; i<l; i++)
  {
    long a=arg[i];
    if (tree[a].f==Fassign)
    {
      long x = detag(tree[a].x);
      if (tree[x].f==Fvec && tree[x].x>=0)
        n += countlisttogen(tree[x].x,Fmatrixelts)-1;
    }
  }
  return n;
}

static void
compileuninline(GEN arg)
{
  long j;
  if (lg(arg) > 1)
    compile_err("too many arguments",tree[arg[1]].str);
  for(j=0; j<s_lvar.n; j++)
    if(!localvars[j].inl)
      pari_err(e_MISC,"uninline is only valid at top level");
  s_lvar.n = 0;
}

static void
compilemy(GEN arg, const char *str, int inl)
{
  long i, j, k, l = lg(arg);
  long n = countvar(arg);
  GEN vep = cgetg(n+1,t_VECSMALL);
  GEN ver = cgetg(n+1,t_VECSMALL);
  if (inl)
  {
    for(j=0; j<s_lvar.n; j++)
      if(!localvars[j].inl)
        pari_err(e_MISC,"inline is only valid at top level");
  }
  for(k=0, i=1; i<l; i++)
  {
    long a=arg[i];
    if (tree[a].f==Fassign)
    {
      long x = detag(tree[a].x);
      if (tree[x].f==Fvec && tree[x].x>=0)
      {
        GEN vars = listtogen(tree[x].x,Fmatrixelts);
        long nv = lg(vars)-1;
        for (j=1; j<=nv; j++)
        {
          ver[++k] = vars[j];
          vep[k] = (long)getvar(ver[k]);
        }
        continue;
      } else ver[++k] = x;
    } else ver[++k] = a;
    vep[k] = (long)getvar(ver[k]);
  }
  checkdups(ver,vep);
  for(i=1; i<=n; i++) var_push(NULL,Lmy);
  op_push_loc(OCnewframe,inl?-n:n,str);
  frame_push(vep);
  for (k=0, i=1; i<l; i++)
  {
    long a=arg[i];
    if (tree[a].f==Fassign)
    {
      long x = detag(tree[a].x);
      if (tree[x].f==Fvec && tree[x].x>=0)
      {
        GEN vars = listtogen(tree[x].x,Fmatrixelts);
        long nv = lg(vars)-1;
        compilenode(tree[a].y,Ggen,FLnocopy);
        if (nv > 1) op_push(OCdup,nv-1,x);
        for (j=1; j<=nv; j++)
        {
          long v = detag(vars[j]);
          op_push(OCpushlong,j,v);
          op_push(OCcompo1,Ggen,v);
          k++;
          op_push(OCstorelex,-n+k-1,a);
          localvars[s_lvar.n-n+k-1].ep=(entree*)vep[k];
          localvars[s_lvar.n-n+k-1].inl=inl;
        }
        continue;
      }
      else if (!is_node_zero(tree[a].y))
      {
        compilenode(tree[a].y,Ggen,FLnocopy);
        op_push(OCstorelex,-n+k,a);
      }
    }
    k++;
    localvars[s_lvar.n-n+k-1].ep=(entree*)vep[k];
    localvars[s_lvar.n-n+k-1].inl=inl;
  }
}

static long
localpush(op_code op, long a)
{
  entree *ep = getvar(a);
  long vep  = (long) ep;
  op_push(op,vep,a);
  var_push(ep,Llocal);
  return vep;
}

static void
compilelocal(GEN arg)
{
  long i, j, k, l = lg(arg);
  long n = countvar(arg);
  GEN vep = cgetg(n+1,t_VECSMALL);
  GEN ver = cgetg(n+1,t_VECSMALL);
  for(k=0, i=1; i<l; i++)
  {
    long a=arg[i];
    if (tree[a].f==Fassign)
    {
      long x = detag(tree[a].x);
      if (tree[x].f==Fvec && tree[x].x>=0)
      {
        GEN vars = listtogen(tree[x].x,Fmatrixelts);
        long nv = lg(vars)-1;
        compilenode(tree[a].y,Ggen,FLnocopy);
        if (nv > 1) op_push(OCdup,nv-1,x);
        for (j=1; j<=nv; j++)
        {
          long v = detag(vars[j]);
          op_push(OCpushlong,j,v);
          op_push(OCcompo1,Ggen,v);
          vep[++k] = localpush(OClocalvar, v);
          ver[k] = v;
        }
        continue;
      } else if (!is_node_zero(tree[a].y))
      {
        compilenode(tree[a].y,Ggen,FLnocopy);
        ver[++k] = x;
        vep[k] = localpush(OClocalvar, ver[k]);
        continue;
      }
      else
        ver[++k] = x;
    } else
      ver[++k] = a;
    vep[k] = localpush(OClocalvar0, ver[k]);
  }
  checkdups(ver,vep);
}

static void
compilefunc(entree *ep, long n, int mode, long flag)
{
  pari_sp ltop=avma;
  long j;
  long x=tree[n].x, y=tree[n].y;
  op_code ret_op;
  long ret_flag;
  Gtype ret_typ;
  char const *p,*q;
  char c;
  const char *flags = NULL;
  const char *str;
  PPproto mod;
  GEN arg=listtogen(y,Flistarg);
  long lnc=first_safe_arg(arg, COsafelex|COsafedyn);
  long lnl=first_safe_arg(arg, COsafelex);
  long nbpointers=0, nbopcodes;
  long nb=lg(arg)-1, lev=0;
  long ev[20];
  if (x>=OPnboperator)
    str=tree[x].str;
  else
  {
    if (nb==2)
      str=tree[arg[1]].str+tree[arg[1]].len;
    else if (nb==1)
      str=tree[arg[1]].str;
    else
      str=tree[n].str;
    while(*str==')') str++;
  }
  if (tree[n].f==Fassign)
  {
    nb=2; lnc=2; lnl=2; arg=mkvecsmall2(x,y);
  }
  else if (is_func_named(ep,"if"))
  {
    if (nb>=4)
      ep=is_entry("_multi_if");
    else if (mode==Gvoid)
      ep=is_entry("_void_if");
  }
  else if (is_func_named(ep,"return") && (flag&FLreturn) && nb<=1)
  {
    if (nb==0) op_push(OCpushgnil,0,n);
    else compilenode(arg[1],Ggen,FLsurvive|FLreturn);
    avma=ltop;
    return;
  }
  else if (is_func_named(ep,"inline"))
  {
    compilemy(arg, str, 1);
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(ep,"uninline"))
  {
    compileuninline(arg);
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(ep,"my"))
  {
    compilemy(arg, str, 0);
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(ep,"local"))
  {
    compilelocal(arg);
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  /*We generate dummy code for global() for compatibility with gp2c*/
  else if (is_func_named(ep,"global"))
  {
    long i;
    for (i=1;i<=nb;i++)
    {
      long a=arg[i];
      long en;
      if (tree[a].f==Fassign)
      {
        compilenode(tree[a].y,Ggen,0);
        a=tree[a].x;
        en=(long)getvar(a);
        op_push(OCstoredyn,en,a);
      }
      else
      {
        en=(long)getvar(a);
        op_push(OCpushdyn,en,a);
        op_push(OCpop,1,a);
      }
    }
    compilecast(n,Gvoid,mode);
    avma=ltop;
    return;
  }
  else if (is_func_named(ep,"O"))
  {
    if (nb!=1)
      compile_err("wrong number of arguments", tree[n].str+tree[n].len-1);
    ep=is_entry("O(_^_)");
    if (tree[arg[1]].f==Ffunction && tree[arg[1]].x==OPpow)
    {
      arg = listtogen(tree[arg[1]].y,Flistarg);
      nb  = lg(arg)-1;
      lnc = first_safe_arg(arg,COsafelex|COsafedyn);
      lnl = first_safe_arg(arg,COsafelex);
    }
  }
  else if (x==OPn && tree[y].f==Fsmall)
  {
    avma=ltop;
    compilesmall(y, -tree[y].x, mode);
    return;
  }
  else if (x==OPtrans && tree[y].f==Fvec)
  {
    avma=ltop;
    compilevec(y, mode, OCcol);
    return;
  }
  else if (x==OPpow && nb==2 && tree[arg[2]].f==Fsmall)
    ep=is_entry("_^s");
  else if (x==OPcat)
    compile_err("expected character: ',' or ')' instead of",
        tree[arg[1]].str+tree[arg[1]].len);
  p=ep->code;
  if (!ep->value)
    compile_err("unknown function",tree[n].str);
  nbopcodes = s_opcode.n;
  ret_op = get_ret_type(&p, ep->arity, &ret_typ, &ret_flag);
  j=1;
  if (*p)
  {
    q=p;
    while((mod=parseproto(&p,&c,tree[n].str))!=PPend)
    {
      if (j<=nb && tree[arg[j]].f!=Fnoarg
          && (mod==PPdefault || mod==PPdefaultmulti))
        mod=PPstd;
      switch(mod)
      {
      case PPstd:
        if (j>nb) compile_err("too few arguments", tree[n].str+tree[n].len-1);
        if (c!='I' && c!='E' && c!='J')
        {
          long x = tree[arg[j]].x, f = tree[arg[j]].f;
          if (f==Fnoarg)
            compile_err("missing mandatory argument", tree[arg[j]].str);
          if (f==Fseq)
            compile_err("unexpected ';'", tree[x].str+tree[x].len);
        }
        switch(c)
        {
        case 'G':
          compilenode(arg[j],Ggen,j>=lnl?(j>=lnc?FLnocopy:FLnocopylex):0);
          j++;
          break;
        case 'W':
          {
            long a = arg[j];
            entree *ep = getlvalue(a);
            long vn = getmvar(ep);
            if (vn) op_push(OCcowvarlex, vn, a);
            else op_push(OCcowvardyn, (long)ep, a);
            compilenode(arg[j++],Ggen,FLnocopy);
            break;
          }
        case 'M':
          if (tree[arg[j]].f!=Fsmall)
          {
            if (!flags) flags = ep->code;
            flags = strchr(flags, '\n'); /* Skip to the following '\n' */
            if (!flags)
              compile_err("missing flag in string function signature",
                           tree[n].str);
            flags++;
            if (tree[arg[j]].f==Fconst && tree[arg[j]].x==CSTstr)
            {
              GEN str=strntoGENexp(tree[arg[j]].str,tree[arg[j]].len);
              op_push(OCpushlong, eval_mnemonic(str, flags),n);
              j++;
            } else
            {
              compilenode(arg[j++],Ggen,0);
              op_push(OCpushlong,(long)flags,n);
              op_push(OCcallgen2,(long)is_entry("_eval_mnemonic"),n);
            }
            break;
          }
        case 'P': case 'L':
          compilenode(arg[j++],Gsmall,0);
          break;
        case 'U':
          compilenode(arg[j++],Gusmall,0);
          break;
        case 'n':
          compilenode(arg[j++],Gvar,0);
          break;
        case '&': case '*':
          {
            long vn, a=arg[j++];
            entree *ep;
            if (c=='&')
            {
              if (tree[a].f!=Frefarg)
                compile_err("expected character: '&'", tree[a].str);
              a=tree[a].x;
            }
            a=detag(a);
            ep=getlvalue(a);
            vn=getmvar(ep);
            if (tree[a].f==Fentry)
            {
              if (vn)
                op_push(OCsimpleptrlex, vn,n);
              else
                op_push(OCsimpleptrdyn, (long)ep,n);
            }
            else
            {
              compilenewptr(vn, ep, a);
              compilelvalue(a);
              op_push(OCpushptr, 0, a);
            }
            nbpointers++;
            break;
          }
        case 'I':
        case 'E':
        case 'J':
          {
            long a = arg[j++];
            GEN  d = compilefuncinline(n, c, a, flag, is_func_named(ep,"if"), lev, ev);
            op_push(OCpushgen, data_push(d), a);
            if (lg(d)==8) op_push(OCsaveframe,FLsurvive,n);
            break;
          }
        case 'V':
          {
            long a = arg[j++];
            (void)getvar(a);
            ev[lev++] = a;
            break;
          }
        case '=':
          {
            long a = arg[j++];
            ev[lev++] = tree[a].x;
            compilenode(tree[a].y, Ggen, FLnocopy);
          }
          break;
        case 'r':
          {
            long a=arg[j++];
            if (tree[a].f==Fentry)
            {
              op_push(OCpushgen, data_push(strntoGENstr(tree[tree[a].x].str,
                                                        tree[tree[a].x].len)),n);
              op_push(OCtostr, -1,n);
            }
            else
            {
              compilenode(a,Ggen,FLnocopy);
              op_push(OCtostr, -1,n);
            }
            break;
          }
        case 's':
          {
            long a = arg[j++];
            GEN g = cattovec(a, OPcat);
            long l, nb = lg(g)-1;
            if (nb==1)
            {
              compilenode(g[1], Ggen, FLnocopy);
              op_push(OCtostr, -1, a);
            } else
            {
              op_push(OCvec, nb+1, a);
              for(l=1; l<=nb; l++)
              {
                compilenode(g[l], Ggen, FLsurvive);
                op_push(OCstackgen,l, a);
              }
              op_push(OCpop, 1, a);
              op_push(OCcallgen,(long)is_entry("Str"), a);
              op_push(OCtostr, -1, a);
            }
            break;
          }
        default:
          pari_err(e_MISC,"Unknown prototype code `%c' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPauto:
        switch(c)
        {
        case 'p':
          op_push(OCprecreal,0,n);
          break;
        case 'b':
          op_push(OCbitprecreal,0,n);
          break;
        case 'P':
          op_push(OCprecdl,0,n);
          break;
        case 'C':
          op_push(OCpushgen,data_push(pack_localvars()),n);
          break;
        case 'f':
          {
            static long foo;
            op_push(OCpushlong,(long)&foo,n);
            break;
          }
        }
        break;
      case PPdefault:
        j++;
        switch(c)
        {
        case 'G':
        case '&':
        case 'E':
        case 'I':
        case 'r':
        case 's':
          op_push(OCpushlong,0,n);
          break;
        case 'n':
          op_push(OCpushlong,-1,n);
          break;
        case 'V':
          ev[lev++] = -1;
          break;
        case 'P':
          op_push(OCprecdl,0,n);
          break;
        default:
          pari_err(e_MISC,"Unknown prototype code `%c' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPdefaultmulti:
        j++;
        switch(c)
        {
        case 'G':
          op_push(OCpushstoi,strtol(q+1,NULL,10),n);
          break;
        case 'L':
        case 'M':
          op_push(OCpushlong,strtol(q+1,NULL,10),n);
          break;
        case 'U':
          op_push(OCpushlong,(long)strtoul(q+1,NULL,10),n);
          break;
        case 'r':
        case 's':
          str_defproto(p, q, tree[n].str);
          op_push(OCtostr, -1, n);
          break;
        default:
          pari_err(e_MISC,"Unknown prototype code `%c' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPstar:
        switch(c)
        {
        case 'E':
          {
            long k, n=nb+1-j;
            GEN g=cgetg(n+1,t_VEC);
            int ismif = is_func_named(ep,"_multi_if");
            for(k=1; k<=n; k++)
              gel(g, k) = compilefuncinline(n, c, arg[j+k-1], flag,
                          ismif && (k==n || odd(k)), lev, ev);
            op_push(OCpushgen, data_push(g), arg[j]);
            j=nb+1;
            break;
          }
        case 's':
          {
            long n=nb+1-j;
            long k,l,l1,m;
            GEN g=cgetg(n+1,t_VEC);
            for(l1=0,k=1;k<=n;k++)
            {
              gel(g,k)=cattovec(arg[j+k-1],OPcat);
              l1+=lg(gel(g,k))-1;
            }
            op_push_loc(OCvec, l1+1, str);
            for(m=1,k=1;k<=n;k++)
              for(l=1;l<lg(gel(g,k));l++,m++)
              {
                compilenode(mael(g,k,l),Ggen,FLsurvive);
                op_push(OCstackgen,m,mael(g,k,l));
              }
            op_push_loc(OCpop, 1, str);
            j=nb+1;
            break;
          }
        default:
          pari_err(e_MISC,"Unknown prototype code `%c*' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      default:
        pari_err_BUG("compilefunc [unknown PPproto]");
      }
      q=p;
    }
  }
  if (j<=nb)
    compile_err("too many arguments",tree[arg[j]].str);
  op_push_loc(ret_op, (long) ep, str);
  if ((ret_flag&FLnocopy) && !(flag&FLnocopy))
    op_push_loc(OCcopy,0,str);
  if (ret_typ==Ggen && nbpointers==0 && s_opcode.n>nbopcodes+128)
  {
    op_insert_loc(nbopcodes,OCavma,0,str);
    op_push_loc(OCgerepile,0,str);
  }
  compilecast(n,ret_typ,mode);
  if (nbpointers) op_push_loc(OCendptr,nbpointers, str);
  avma=ltop;
}

static void
genclosurectx(const char *loc, long nbdata)
{
  long i;
  GEN vep = cgetg(nbdata+1,t_VECSMALL);
  for(i = 1; i <= nbdata; i++)
  {
    vep[i] = 0;
    op_push_loc(OCpushlex,-i,loc);
  }
  frame_push(vep);
}

static GEN
genclosure(entree *ep, const char *loc, long  nbdata, int check)
{
  pari_sp av = avma;
  struct codepos pos;
  long nb=0;
  const char *code=ep->code,*p,*q;
  char c;
  GEN text;
  long index=ep->arity;
  long arity=0, maskarg=0, maskarg0=0, stop=0, dovararg=0;
  PPproto mod;
  Gtype ret_typ;
  long ret_flag;
  op_code ret_op=get_ret_type(&code,ep->arity,&ret_typ,&ret_flag);
  p=code;
  while ((mod=parseproto(&p,&c,NULL))!=PPend)
  {
    if (mod==PPauto)
      stop=1;
    else
    {
      if (stop) return NULL;
      if (c=='V') continue;
      maskarg<<=1; maskarg0<<=1; arity++;
      switch(mod)
      {
      case PPstd:
        maskarg|=1L;
        break;
      case PPdefault:
        switch(c)
        {
        case '&':
        case 'E':
        case 'I':
          maskarg0|=1L;
          break;
        }
        break;
      default:
        break;
      }
    }
  }
  if (check && EpSTATIC(ep) && maskarg==0)
    return gen_0;
  getcodepos(&pos);
  dbgstart = loc;
  if (nbdata > arity)
    pari_err(e_MISC,"too many parameters for closure `%s'", ep->name);
  if (nbdata) genclosurectx(loc, nbdata);
  text = strtoGENstr(ep->name);
  arity -= nbdata;
  if (maskarg)  op_push_loc(OCcheckargs,maskarg,loc);
  if (maskarg0) op_push_loc(OCcheckargs0,maskarg0,loc);
  p=code;
  while ((mod=parseproto(&p,&c,NULL))!=PPend)
  {
    switch(mod)
    {
    case PPauto:
      switch(c)
      {
      case 'p':
        op_push_loc(OCprecreal,0,loc);
        break;
      case 'b':
        op_push_loc(OCbitprecreal,0,loc);
        break;
      case 'P':
        op_push_loc(OCprecdl,0,loc);
        break;
      case 'C':
        op_push_loc(OCpushgen,data_push(pack_localvars()),loc);
        break;
      case 'f':
        {
          static long foo;
          op_push_loc(OCpushlong,(long)&foo,loc);
          break;
        }
      }
    default:
      break;
    }
  }
  q = p = code;
  while ((mod=parseproto(&p,&c,NULL))!=PPend)
  {
    switch(mod)
    {
    case PPstd:
      switch(c)
      {
      case 'G':
        break;
      case 'M':
      case 'L':
        op_push_loc(OCitos,-index,loc);
        break;
      case 'U':
        op_push_loc(OCitou,-index,loc);
        break;
      case 'n':
        op_push_loc(OCvarn,-index,loc);
        break;
      case '&': case '*':
      case 'I':
      case 'E':
      case 'V':
      case '=':
        return NULL;
      case 'r':
      case 's':
        op_push_loc(OCtostr,-index,loc);
        break;
      }
      break;
    case PPauto:
      break;
    case PPdefault:
      switch(c)
      {
      case 'G':
      case '&':
      case 'E':
      case 'I':
      case 'V':
      case 'r':
      case 's':
        break;
      case 'n':
        op_push_loc(OCvarn,-index,loc);
        break;
      case 'P':
        op_push_loc(OCprecdl,0,loc);
        op_push_loc(OCdefaultlong,-index,loc);
        break;
      default:
        pari_err(e_MISC,"Unknown prototype code `D%c' for `%s'",c,ep->name);
      }
      break;
    case PPdefaultmulti:
      switch(c)
      {
      case 'G':
        op_push_loc(OCpushstoi,strtol(q+1,NULL,10),loc);
        op_push_loc(OCdefaultgen,-index,loc);
        break;
      case 'L':
      case 'M':
        op_push_loc(OCpushlong,strtol(q+1,NULL,10),loc);
        op_push_loc(OCdefaultlong,-index,loc);
        break;
      case 'U':
        op_push_loc(OCpushlong,(long)strtoul(q+1,NULL,10),loc);
        op_push_loc(OCdefaultulong,-index,loc);
        break;
      case 'r':
      case 's':
        str_defproto(p, q, loc);
        op_push_loc(OCdefaultgen,-index,loc);
        op_push_loc(OCtostr,-index,loc);
        break;
      default:
        pari_err(e_MISC,
            "Unknown prototype code `D...,%c,' for `%s'",c,ep->name);
      }
      break;
    case PPstar:
      switch(c)
      {
      case 's':
        dovararg = 1;
        break;
      case 'E':
        return NULL;
      default:
        pari_err(e_MISC,"Unknown prototype code `%c*' for `%s'",c,ep->name);
      }
      break;
    default:
      return NULL;
    }
    index--;
    q = p;
  }
  op_push_loc(ret_op, (long) ep, loc);
  if (ret_flag==FLnocopy) op_push_loc(OCcopy,0,loc);
  compilecast_loc(ret_typ, Ggen, loc);
  if (dovararg) nb|=VARARGBITS;
  return gerepilecopy(av, getfunction(&pos,nb+arity,nbdata,text,0));
}

GEN
snm_closure(entree *ep, GEN data)
{
  long i;
  long n = data ? lg(data)-1: 0;
  GEN C = genclosure(ep,ep->name,n,0);
  for(i=1; i<=n; i++)
    gmael(C,7,i) = gel(data,i);
  return C;
}

GEN
strtoclosure(const char *s, long n,  ...)
{
  pari_sp av = avma;
  entree *ep = is_entry(s);
  GEN C;
  if (!ep) pari_err(e_NOTFUNC, strtoGENstr(s));
  ep = do_alias(ep);
  if ((!EpSTATIC(ep) && EpVALENCE(ep)!=EpINSTALL) || !ep->value)
    pari_err(e_MISC,"not a built-in/install'ed function: \"%s\"",s);
  C = genclosure(ep,ep->name,n,0);
  if (!C) pari_err(e_MISC,"function prototype unsupported: \"%s\"",s);
  else
  {
    va_list ap;
    long i;
    va_start(ap,n);
    for(i=1; i<=n; i++)
      gmael(C,7,i) = va_arg(ap, GEN);
    va_end(ap);
  }
  return gerepilecopy(av, C);
}

GEN
strtofunction(const char *s)
{
  return strtoclosure(s, 0);
}

GEN
call0(GEN fun, GEN args)
{
  if (!is_vec_t(typ(args))) pari_err_TYPE("call",args);
  switch(typ(fun))
  {
    case t_STR:
      fun = strtofunction(GSTR(fun));
    case t_CLOSURE: /* fall through */
      return closure_callgenvec(fun, args);
    default:
      pari_err_TYPE("call", fun);
      return NULL; /* LCOV_EXCL_LINE */
  }
}

static void
closurefunc(entree *ep, long n, long mode)
{
  pari_sp ltop=avma;
  GEN C;
  if (!ep->value) compile_err("unknown function",tree[n].str);
  C = genclosure(ep,tree[n].str,0,1);
  if (!C) compile_err("sorry, closure not implemented",tree[n].str);
  if (C==gen_0)
  {
    compilefunc(ep,n,mode,0);
    return;
  }
  op_push(OCpushgen, data_push(C), n);
  compilecast(n,Gclosure,mode);
  avma=ltop;
}

static void
compileseq(long n, int mode, long flag)
{
  pari_sp av = avma;
  GEN L = listtogen(n, Fseq);
  long i, l = lg(L)-1;
  for(i = 1; i < l; i++)
    compilenode(L[i],Gvoid,0);
  compilenode(L[l],mode,flag&(FLreturn|FLsurvive));
  avma = av;
}

static void
compilenode(long n, int mode, long flag)
{
  long x,y;
#ifdef STACK_CHECK
  if (PARI_stack_limit && (void*) &x <= PARI_stack_limit)
    pari_err(e_MISC, "expression nested too deeply");
#endif
  if (n<0) pari_err_BUG("compilenode");
  x=tree[n].x;
  y=tree[n].y;

  switch(tree[n].f)
  {
  case Fseq:
    compileseq(n, mode, flag);
    return;
  case Fmatcoeff:
    compilematcoeff(n,mode);
    if (mode==Ggen && !(flag&FLnocopy))
      op_push(OCcopy,0,n);
    return;
  case Fassign:
    x = detag(x);
    if (tree[x].f==Fvec && tree[x].x>=0)
    {
      GEN vars = listtogen(tree[x].x,Fmatrixelts);
      long i, l = lg(vars)-1, d = mode==Gvoid? l-1: l;
      compilenode(y,Ggen,mode==Gvoid?0:flag&FLsurvive);
      if (d) op_push(OCdup, d, x);
      for(i=1; i<=l; i++)
      {
        long a = detag(vars[i]);
        entree *ep=getlvalue(a);
        long vn=getmvar(ep);
        op_push(OCpushlong,i,a);
        op_push(OCcompo1,Ggen,a);
        if (tree[a].f==Fentry)
          compilestore(vn,ep,n);
        else
        {
          compilenewptr(vn,ep,n);
          compilelvalue(a);
          op_push(OCstoreptr,0,a);
        }
      }
      if (mode!=Gvoid)
        compilecast(n,Ggen,mode);
    }
    else
    {
      entree *ep=getlvalue(x);
      long vn=getmvar(ep);
      if (tree[x].f!=Fentry)
      {
        compilenewptr(vn,ep,n);
        compilelvalue(x);
      }
      compilenode(y,Ggen,mode==Gvoid?FLnocopy:flag&FLsurvive);
      if (mode!=Gvoid)
        op_push(OCdup,1,n);
      if (tree[x].f==Fentry)
        compilestore(vn,ep,n);
      else
        op_push(OCstoreptr,0,x);
      if (mode!=Gvoid)
        compilecast(n,Ggen,mode);
    }
    return;
  case Fconst:
    {
      pari_sp ltop=avma;
      if (tree[n].x!=CSTquote)
      {
        if (mode==Gvoid) return;
        if (mode==Gvar) compile_varerr(tree[n].str);
      }
      if (mode==Gsmall)
        compile_err("this should be a small integer", tree[n].str);
      switch(tree[n].x)
      {
      case CSTreal:
        op_push(OCpushreal, data_push(strntoGENstr(tree[n].str,tree[n].len)),n);
        break;
      case CSTint:
        op_push(OCpushgen,  data_push(strtoi((char*)tree[n].str)),n);
        compilecast(n,Ggen, mode);
        break;
      case CSTstr:
        op_push(OCpushgen,  data_push(strntoGENexp(tree[n].str,tree[n].len)),n);
        break;
      case CSTquote:
        { /* skip ' */
          entree *ep = fetch_entry_raw(tree[n].str+1,tree[n].len-1);
          if (EpSTATIC(ep)) compile_varerr(tree[n].str+1);
          op_push(OCpushvar, (long)ep,n);
          compilecast(n,Ggen, mode);
          break;
        }
      default:
        pari_err_BUG("compilenode, unsupported constant");
      }
      avma=ltop;
      return;
    }
  case Fsmall:
    compilesmall(n, x, mode);
    return;
  case Fvec:
    compilevec(n, mode, OCvec);
    return;
  case Fmat:
    compilemat(n, mode);
    return;
  case Frefarg:
    compile_err("unexpected character '&':",tree[n].str);
    return;
  case Fentry:
    {
      entree *ep=getentry(n);
      long vn=getmvar(ep);
      if (vn)
      {
        op_push(OCpushlex,(long)vn,n);
        addcopy(n,mode,flag,FLnocopy|FLnocopylex);
        compilecast(n,Ggen,mode);
      }
      else if (ep->valence==EpVAR || ep->valence==EpNEW)
      {
        if (DEBUGLEVEL && mode==Gvoid)
          pari_warn(warner,"statement with no effect: `%s'",ep->name);
        op_push(OCpushdyn,(long)ep,n);
        addcopy(n,mode,flag,FLnocopy);
        compilecast(n,Ggen,mode);
      }
      else
        closurefunc(ep,n,mode);
      return;
    }
  case Ffunction:
    {
      entree *ep=getfunc(n);
      if (EpVALENCE(ep)==EpVAR || EpVALENCE(ep)==EpNEW)
      {
        if (tree[n].x<OPnboperator) /* should not happen */
          compile_err("operator unknown",tree[n].str);
        compilecall(n,mode,ep);
      }
      else
        compilefunc(ep,n,mode,flag);
      return;
    }
  case Fcall:
    compilecall(n,mode,NULL);
    return;
  case Flambda:
    {
      pari_sp ltop=avma;
      struct codepos pos;
      GEN arg=listtogen(x,Flistarg);
      long nb, lgarg, nbmvar, dovararg=0, gap;
      long strict = GP_DATA->strictargs;
      GEN vep = cgetg_copy(arg, &lgarg);
      GEN text=cgetg(3,t_VEC);
      gel(text,1)=strntoGENstr(tree[x].str,tree[x].len);
      gel(text,2)=strntoGENstr(tree[y].str,tree[y].len);
      getcodepos(&pos);
      dbgstart=tree[x].str+tree[x].len;
      gap = tree[y].str-dbgstart;
      nbmvar=ctxmvar();
      nb = lgarg-1;
      if (nb)
      {
        long i;
        for(i=1;i<=nb;i++)
        {
          long a=arg[i];
          if (i==nb && tree[a].f==Fvararg)
          {
            dovararg=1;
            vep[i]=(long)getvar(tree[a].x);
          }
          else
            vep[i]=(long)getvar(tree[a].f==Fassign?tree[a].x:a);
          var_push(NULL,Lmy);
        }
        checkdups(arg,vep);
        op_push(OCgetargs,nb,x);
        frame_push(vep);
        for (i=1;i<=nb;i++)
        {
          long a=arg[i];
          long y = tree[a].y;
          if (tree[a].f==Fassign && (strict || !is_node_zero(y)))
          {
            if (tree[y].f==Fsmall)
              compilenode(y, Ggen, 0);
            else
            {
              struct codepos lpos;
              getcodepos(&lpos);
              compilenode(y, Ggen, 0);
              op_push(OCpushgen, data_push(getclosure(&lpos)),a);
            }
            op_push(OCdefaultarg,-nb+i-1,a);
          }
          localvars[s_lvar.n-nb+i-1].ep=(entree*)vep[i];
        }
      }
      if (strict)
        op_push(OCcheckuserargs,nb,x);
      dbgstart=tree[y].str;
      if (y>=0 && tree[y].f!=Fnoarg)
        compilenode(y,Ggen,FLsurvive|FLreturn);
      else
        compilecast(n,Gvoid,Ggen);
      if (dovararg) nb|=VARARGBITS;
      op_push(OCpushgen, data_push(getfunction(&pos,nb,nbmvar,text,gap)),n);
      if (nbmvar) op_push(OCsaveframe,!!(flag&FLsurvive),n);
      compilecast(n, Gclosure, mode);
      avma=ltop;
      return;
    }
  case Ftag:
    compilenode(x, mode,flag);
    return;
  case Fnoarg:
    compilecast(n,Gvoid,mode);
    return;
  case Fnorange:
    op_push(OCpushlong,LONG_MAX,n);
    compilecast(n,Gsmall,mode);
    return;
  default:
    pari_err_BUG("compilenode");
  }
}

GEN
gp_closure(long n)
{
  struct codepos pos;
  getcodepos(&pos);
  dbgstart=tree[n].str;
  compilenode(n,Ggen,FLsurvive|FLreturn);
  return getfunction(&pos,0,0,strntoGENstr(tree[n].str,tree[n].len),0);
}

GEN
closure_deriv(GEN G)
{
  pari_sp ltop=avma;
  long i;
  struct codepos pos;
  const char *code;
  GEN text;
  long arity=closure_arity(G);
  if (arity==0 || closure_is_variadic(G))
    pari_err_TYPE("derivfun",G);
  if (typ(gel(G,6))==t_STR)
  {
    code = GSTR(gel(G,6));
    text = cgetg(1+nchar2nlong(2+strlen(code)),t_STR);
    sprintf(GSTR(text),"%s'",code);
  }
  else
  {
    code = GSTR(GENtoGENstr(G));
    text = cgetg(1+nchar2nlong(4+strlen(code)),t_STR);
    sprintf(GSTR(text),"(%s)'",code);
  }
  getcodepos(&pos);
  dbgstart=code;
  op_push_loc(OCgetargs, arity,code);
  op_push_loc(OCpushgen,data_push(G),code);
  op_push_loc(OCvec,arity+1,code);
  for (i=1;i<=arity;i++)
  {
    op_push_loc(OCpushlex,i-arity-1,code);
    op_push_loc(OCstackgen,i,code);
  }
  op_push_loc(OCpop,1,code);
  op_push_loc(OCprecreal,0,code);
  op_push_loc(OCcallgen,(long)is_entry("_derivfun"),code);
  return gerepilecopy(ltop, getfunction(&pos,arity,0,text,0));
}

static long
vec_optimize(GEN arg)
{
  long fl = COsafelex|COsafedyn;
  long i;
  for (i=1; i<lg(arg); i++)
  {
    optimizenode(arg[i]);
    fl &= tree[arg[i]].flags;
  }
  return fl;
}

static void
optimizevec(long n)
{
  pari_sp ltop=avma;
  long x = tree[n].x;
  GEN  arg = listtogen(x, Fmatrixelts);
  tree[n].flags = vec_optimize(arg);
  avma = ltop;
}

static void
optimizemat(long n)
{
  pari_sp ltop = avma;
  long x = tree[n].x;
  long i;
  GEN line = listtogen(x,Fmatrixlines);
  long fl = COsafelex|COsafedyn;
  for(i=1;i<lg(line);i++)
  {
    GEN col=listtogen(line[i],Fmatrixelts);
    fl &= vec_optimize(col);
  }
  avma=ltop; tree[n].flags=fl;
}

static void
optimizematcoeff(long n)
{
  long x=tree[n].x;
  long y=tree[n].y;
  long yx=tree[y].x;
  long yy=tree[y].y;
  long fl;
  optimizenode(x);
  optimizenode(yx);
  fl=tree[x].flags&tree[yx].flags;
  if (yy>=0)
  {
    optimizenode(yy);
    fl&=tree[yy].flags;
  }
  tree[n].flags=fl;
}


static void
optimizefunc(entree *ep, long n)
{
  pari_sp av=avma;
  long j;
  long x=tree[n].x;
  long y=tree[n].y;
  Gtype t;
  PPproto mod;
  long fl=COsafelex|COsafedyn;
  const char *p;
  char c;
  GEN arg = listtogen(y,Flistarg);
  long nb=lg(arg)-1, ret_flag;
  if (is_func_named(ep,"if") && nb>=4)
    ep=is_entry("_multi_if");
  p = ep->code;
  if (!p)
    fl=0;
  else
    (void) get_ret_type(&p, 2, &t, &ret_flag);
  if (p && *p)
  {
    j=1;
    while((mod=parseproto(&p,&c,tree[n].str))!=PPend)
    {
      if (j<=nb && tree[arg[j]].f!=Fnoarg
          && (mod==PPdefault || mod==PPdefaultmulti))
        mod=PPstd;
      switch(mod)
      {
      case PPstd:
        if (j>nb) compile_err("too few arguments", tree[n].str+tree[n].len-1);
        if (tree[arg[j]].f==Fnoarg && c!='I' && c!='E')
          compile_err("missing mandatory argument", tree[arg[j]].str);
        switch(c)
        {
        case 'G':
        case 'n':
        case 'M':
        case 'L':
        case 'U':
        case 'P':
          optimizenode(arg[j]);
          fl&=tree[arg[j++]].flags;
          break;
        case 'I':
        case 'E':
        case 'J':
          optimizenode(arg[j]);
          fl&=tree[arg[j]].flags;
          tree[arg[j++]].flags=COsafelex|COsafedyn;
          break;
        case '&': case '*':
          {
            long a=arg[j];
            if (c=='&')
            {
              if (tree[a].f!=Frefarg)
                compile_err("expected character: '&'", tree[a].str);
              a=tree[a].x;
            }
            optimizenode(a);
            tree[arg[j++]].flags=COsafelex|COsafedyn;
            fl=0;
            break;
          }
        case 'W':
          optimizenode(arg[j++]);
          fl=0;
          break;
        case 'V':
        case 'r':
          tree[arg[j++]].flags=COsafelex|COsafedyn;
          break;
        case '=':
          {
            long a=arg[j++], y=tree[a].y;
            if (tree[a].f!=Fassign)
              compile_err("expected character: '=' instead of",
                  tree[a].str+tree[a].len);
            optimizenode(y);
            fl&=tree[y].flags;
          }
          break;
        case 's':
          fl &= vec_optimize(cattovec(arg[j++], OPcat));
          break;
        default:
          pari_err(e_MISC,"Unknown prototype code `%c' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      case PPauto:
        break;
      case PPdefault:
      case PPdefaultmulti:
        if (j<=nb) optimizenode(arg[j++]);
        break;
      case PPstar:
        switch(c)
        {
        case 'E':
          {
            long n=nb+1-j;
            long k;
            for(k=1;k<=n;k++)
            {
              optimizenode(arg[j+k-1]);
              fl &= tree[arg[j+k-1]].flags;
            }
            j=nb+1;
            break;
          }
        case 's':
          {
            long n=nb+1-j;
            long k;
            for(k=1;k<=n;k++)
              fl &= vec_optimize(cattovec(arg[j+k-1],OPcat));
            j=nb+1;
            break;
          }
        default:
          pari_err(e_MISC,"Unknown prototype code `%c*' for `%.*s'",c,
              tree[x].len, tree[x].str);
        }
        break;
      default:
        pari_err_BUG("optimizefun [unknown PPproto]");
      }
    }
    if (j<=nb)
      compile_err("too many arguments",tree[arg[j]].str);
  }
  else (void)vec_optimize(arg);
  avma=av; tree[n].flags=fl;
}

static void
optimizecall(long n)
{
  pari_sp av=avma;
  long x=tree[n].x;
  long y=tree[n].y;
  GEN arg=listtogen(y,Flistarg);
  optimizenode(x);
  tree[n].flags = COsafelex&tree[x].flags&vec_optimize(arg);
  avma=av;
}

static void
optimizeseq(long n)
{
  pari_sp av = avma;
  GEN L = listtogen(n, Fseq);
  long i, l = lg(L)-1, flags=-1L;
  for(i = 1; i <= l; i++)
  {
    optimizenode(L[i]);
    flags &= tree[L[i]].flags;
  }
  avma = av;
  tree[n].flags = flags;
}

void
optimizenode(long n)
{
  long x,y;
#ifdef STACK_CHECK
  if (PARI_stack_limit && (void*) &x <= PARI_stack_limit)
    pari_err(e_MISC, "expression nested too deeply");
#endif
  if (n<0)
    pari_err_BUG("optimizenode");
  x=tree[n].x;
  y=tree[n].y;

  switch(tree[n].f)
  {
  case Fseq:
    optimizeseq(n);
    return;
  case Frange:
    optimizenode(x);
    optimizenode(y);
    tree[n].flags=tree[x].flags&tree[y].flags;
    break;
  case Fmatcoeff:
    optimizematcoeff(n);
    break;
  case Fassign:
    optimizenode(x);
    optimizenode(y);
    tree[n].flags=0;
    break;
  case Fnoarg:
  case Fnorange:
  case Fsmall:
  case Fconst:
  case Fentry:
    tree[n].flags=COsafelex|COsafedyn;
    return;
  case Fvec:
    optimizevec(n);
    return;
  case Fmat:
    optimizemat(n);
    return;
  case Frefarg:
    compile_err("unexpected character '&'",tree[n].str);
    return;
  case Fvararg:
    compile_err("unexpected characters '..'",tree[n].str);
    return;
  case Ffunction:
    {
      entree *ep=getfunc(n);
      if (EpVALENCE(ep)==EpVAR || EpVALENCE(ep)==EpNEW)
        optimizecall(n);
      else
        optimizefunc(ep,n);
      return;
    }
  case Fcall:
    optimizecall(n);
    return;
  case Flambda:
    optimizenode(y);
    tree[n].flags=COsafelex|COsafedyn;
    return;
  case Ftag:
    optimizenode(x);
    tree[n].flags=tree[x].flags;
    return;
  default:
    pari_err_BUG("optimizenode");
  }
}
