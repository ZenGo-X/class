/* $Id$

Copyright (C) 2013  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */
#include "pari.h"
#include "paripriv.h"
#include "mt.h"

static GEN
mtsingle_queue_get(struct mt_state *mt, long *workid, long *pending)
{
  GEN done = mt->pending;
  if (workid) *workid = mt->workid;
  mt->pending = NULL; *pending = 0;
  return done;
}

static void
mtsingle_queue_submit(struct mt_state *mt, long workid, GEN work)
{
  mt->pending = work? closure_callgenvec(mt->worker, work): NULL;
  mt->workid = workid;
}

static void
mtsingle_queue_end(void) {  }

void
mtsingle_queue_start(struct pari_mt *pt, GEN worker)
{
  pt->get = mtsingle_queue_get;
  pt->submit = mtsingle_queue_submit;
  pt->end = mtsingle_queue_end;
  pt->mt.worker = worker;
  pt->mt.pending = NULL;
}

void
mt_queue_end(struct pari_mt *pt) { pt->end(); }

void
mt_queue_submit(struct pari_mt *pt, long workid, GEN work)
{ pt->submit(&pt->mt, workid, work); }

GEN
mt_queue_get(struct pari_mt *pt, long *workid, long *pending)
{ return pt->get(&pt->mt, workid, pending); }

void
mt_queue_start(struct pari_mt *pt, GEN worker)
{ return mt_queue_start_lim(pt, worker, 0); }

void
mtstate_save(long *pending)
{
  *pending = mt_is_parallel();
}

void
mtstate_restore(long *pending)
{
  if (!*pending && mt_is_parallel())
    mt_queue_reset();
}

void
mtstate_reset(void)
{
  if (mt_is_parallel())
    mt_queue_reset();
}
