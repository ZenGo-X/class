/* Copyright (C) 2013  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
#include <pthread.h>
#include "pari.h"
#include "paripriv.h"
#include "mt.h"
#if defined(_WIN32)
#  include "../systems/mingw/mingw.h"
#endif

struct mt_queue
{
  long no;
  pari_sp avma;
  struct pari_mainstack *mainstack;
  GEN input, output;
  GEN worker;
  long workid;
  pthread_cond_t cond;
  pthread_mutex_t mut;
  pthread_cond_t *pcond;
  pthread_mutex_t *pmut;
};

struct mt_pstate
{
  pthread_t *th;
  struct pari_thread *pth;
  struct mt_queue *mq;
  long n, nbint, last;
  long pending;
  pthread_cond_t pcond;
  pthread_mutex_t pmut;
};

static THREAD long mt_thread_no = -1;
static struct mt_pstate *pari_mt;

#define LOCK(x) pthread_mutex_lock(x); do
#define UNLOCK(x) while(0); pthread_mutex_unlock(x)

void
mt_sigint_block(void)
{
  if (mt_thread_no>=0)
    pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED,NULL);
}

void
mt_sigint_unblock(void)
{
  if (mt_thread_no>=0)
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS,NULL);
}

void
mt_err_recover(long er)
{
  (void) er;
  if (mt_thread_no>=0)
  {
    struct mt_pstate *mt = pari_mt;
    struct mt_queue *mq = mt->mq+mt_thread_no;
    GEN err = pari_err_last();
    err = err_get_num(err)==e_STACK ? err_e_STACK: bin_copy(copy_bin(err));
    LOCK(mq->pmut)
    {
      mq->output = err;
      pthread_cond_signal(mq->pcond);
    } UNLOCK(mq->pmut);
    pthread_exit((void*)1);
  }
}

void
mt_sigint(void)
{
  if (pari_mt) pthread_cond_broadcast(&pari_mt->pcond);
}

int
mt_is_parallel(void)
{
  return !!pari_mt;
}

int
mt_is_thread(void)
{
  return mt_thread_no>=0;
}

void mt_broadcast(GEN code) {(void) code;}

void pari_mt_init(void)
{
  pari_mt = NULL;
#ifdef _SC_NPROCESSORS_CONF
  if (!pari_mt_nbthreads) pari_mt_nbthreads = sysconf(_SC_NPROCESSORS_CONF);
#elif defined(_WIN32)
  if (!pari_mt_nbthreads) pari_mt_nbthreads = win32_nbthreads();
#else
  pari_mt_nbthreads = 1;
#endif
}

void pari_mt_close(void) { }

static void
mt_queue_cleanup(void *arg)
{
  (void) arg;
  pari_thread_close();
}

static void*
mt_queue_run(void *arg)
{
  GEN args = pari_thread_start((struct pari_thread*) arg);
  pari_sp av = avma;
  struct mt_queue *mq = (struct mt_queue *) args;
  mt_thread_no = mq->no;
  pthread_cleanup_push(mt_queue_cleanup,NULL);
  LOCK(mq->pmut)
  {
    mq->mainstack = pari_mainstack;
    mq->avma = av;
    pthread_cond_signal(mq->pcond);
  } UNLOCK(mq->pmut);
  for(;;)
  {
    GEN work, done;
    LOCK(&mq->mut)
    {
      while(!mq->input)
        pthread_cond_wait(&mq->cond, &mq->mut);
    } UNLOCK(&mq->mut);
    pari_mainstack = mq->mainstack;
    avma = mq->avma;
    work = mq->input;
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS,NULL);
    done = closure_callgenvec(mq->worker,work);
    pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED,NULL);
    LOCK(mq->pmut)
    {
      mq->mainstack = pari_mainstack;
      mq->avma = av;
      mq->input = NULL;
      mq->output = done;
      pthread_cond_signal(mq->pcond);
    } UNLOCK(mq->pmut);
  }
  pthread_cleanup_pop(1);
#ifdef __GNUC__
  return NULL; /* LCOV_EXCL_LINE */
#endif
}

static long
mt_queue_check(struct mt_pstate *mt)
{
  long i;
  for(i=0; i<mt->n; i++)
  {
    struct mt_queue *mq = mt->mq+i;
    if (mq->output) return i;
  }
  return -1;
}

static GEN
mtpthread_queue_get(struct mt_state *junk, long *workid, long *pending)
{
  struct mt_pstate *mt = pari_mt;
  struct mt_queue *mq;
  GEN done = NULL;
  long last;
  (void) junk;
  if (mt->nbint<mt->n)
  {
    mt->last = mt->nbint;
    *pending = mt->pending;
    return NULL;
  }
  BLOCK_SIGINT_START
  LOCK(&mt->pmut)
  {
    while ((last = mt_queue_check(mt)) < 0)
    {
      pthread_cond_wait(&mt->pcond, &mt->pmut);
      if (PARI_SIGINT_pending)
      {
        int sig = PARI_SIGINT_pending;
        PARI_SIGINT_pending = 0;
        pthread_mutex_unlock(&mt->pmut);
        PARI_SIGINT_block = 0;
        raise(sig);
        PARI_SIGINT_block = 1;
        pthread_mutex_lock(&mt->pmut);
      }
    }
  } UNLOCK(&mt->pmut);
  BLOCK_SIGINT_END
  mq = mt->mq+last;
  done = gcopy(mq->output);
  mq->output = NULL;
  if (workid) *workid = mq->workid;
  if (typ(done) == t_ERROR)
  {
    if (err_get_num(done)==e_STACK)
      pari_err(e_STACKTHREAD);
    else
      pari_err(0,done);
  }
  mt->last = last;
  mt->pending--;
  *pending = mt->pending;
  return done;
}

static void
mtpthread_queue_submit(struct mt_state *junk, long workid, GEN work)
{
  struct mt_pstate *mt = pari_mt;
  struct mt_queue *mq = mt->mq+mt->last;
  (void) junk;
  if (!work) { mt->nbint=mt->n; return; }
  BLOCK_SIGINT_START
  if (mt->nbint<mt->n)
  {
    mt->nbint++;
    LOCK(mq->pmut)
    {
      while(!mq->avma)
        pthread_cond_wait(mq->pcond, mq->pmut);
    } UNLOCK(mq->pmut);
  }
  LOCK(&mq->mut)
  {
    mq->output = NULL;
    mq->workid = workid;
    BLOCK_SIGINT_START
    {
      pari_sp av = avma;
      struct pari_mainstack *st = pari_mainstack;
      pari_mainstack = mq->mainstack;
      avma = mq->avma;
      mq->input = gcopy(work);
      mq->avma = avma;
      mq->mainstack = pari_mainstack;
      pari_mainstack = st;
      avma = av;
    }
    BLOCK_SIGINT_END
    pthread_cond_signal(&mq->cond);
  } UNLOCK(&mq->mut);
  mt->pending++;
  BLOCK_SIGINT_END
}

void
mt_queue_reset(void)
{
  struct mt_pstate *mt = pari_mt;
  long i;
  BLOCK_SIGINT_START
  for (i=0; i<mt->n; i++)
    pthread_cancel(mt->th[i]);
  for (i=0; i<mt->n; i++)
    pthread_join(mt->th[i],NULL);
  pari_mt = NULL;
  BLOCK_SIGINT_END
  if (DEBUGLEVEL) pari_warn(warner,"stopping %ld threads", mt->n);
  for (i=0;i<mt->n;i++)
  {
    struct mt_queue *mq = mt->mq+i;
    pthread_cond_destroy(&mq->cond);
    pthread_mutex_destroy(&mq->mut);
    pari_thread_free(&mt->pth[i]);
  }
  pari_free(mt->mq);
  pari_free(mt->pth);
  pari_free(mt->th);
  pari_free(mt);
}

static long
closure_has_clone(GEN fun)
{
  if (isclone(fun)) return 1;
  if (lg(fun) >= 8)
  {
    GEN f = closure_get_frame(fun);
    long i, l = lg(f);
    for (i = 1; i < l; i++)
      if (isclone(gel(f,i))) return 1;
  }
  return 0;
}

void
mt_queue_start_lim(struct pari_mt *pt, GEN worker, long lim)
{
  if (lim==0) lim = pari_mt_nbthreads;
  else        lim = minss(pari_mt_nbthreads, lim);
  if (pari_mt || lim <= 1)
    mtsingle_queue_start(pt, worker);
  else
  {
    struct mt_pstate *mt =
           (struct mt_pstate*) pari_malloc(sizeof(struct mt_pstate));
    long mtparisize = GP_DATA->threadsize? GP_DATA->threadsize: pari_mainstack->rsize;
    long mtparisizemax = GP_DATA->threadsizemax;
    long i;
    if (closure_has_clone(worker))
      worker = gcopy(worker); /* to avoid clone_lock race */
    mt->mq  = (struct mt_queue *) pari_malloc(sizeof(*mt->mq)*lim);
    mt->th  = (pthread_t *) pari_malloc(sizeof(*mt->th)*lim);
    mt->pth = (struct pari_thread *) pari_malloc(sizeof(*mt->pth)*lim);
    mt->pending = 0;
    mt->n = lim;
    mt->nbint = 0;
    mt->last = 0;
    pthread_cond_init(&mt->pcond,NULL);
    pthread_mutex_init(&mt->pmut,NULL);
    pari_thread_sync();
    for (i=0;i<lim;i++)
    {
      struct mt_queue *mq = mt->mq+i;
      mq->no     = i;
      mq->avma   = 0;
      mq->mainstack = NULL;
      mq->worker = worker;
      mq->input  = NULL;
      mq->output = NULL;
      mq->pcond  = &mt->pcond;
      mq->pmut   = &mt->pmut;
      pthread_cond_init(&mq->cond,NULL);
      pthread_mutex_init(&mq->mut,NULL);
      if (mtparisizemax)
        pari_thread_valloc(&mt->pth[i],mtparisize,mtparisizemax,(GEN)mq);
      else
        pari_thread_alloc(&mt->pth[i],mtparisize,(GEN)mq);
    }
    if (DEBUGLEVEL) pari_warn(warner,"starting %ld threads", lim);
    BLOCK_SIGINT_START
    for (i=0;i<lim;i++)
      pthread_create(&mt->th[i],NULL, &mt_queue_run, (void*)&mt->pth[i]);
    pari_mt = mt;
    BLOCK_SIGINT_END
    pt->get=&mtpthread_queue_get;
    pt->submit=&mtpthread_queue_submit;
    pt->end=&mt_queue_reset;
  }
}
