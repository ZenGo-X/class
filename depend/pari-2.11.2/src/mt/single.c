/* Copyright (C) 2013  The PARI group.

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
#include "mt.h"

void mt_sigint_block(void) { }
void mt_sigint_unblock(void) { }
void mt_err_recover(long er) { (void)er; }
void pari_mt_close(void) { }
void mt_queue_reset(void) { }
void mt_broadcast(GEN code) {(void) code;}

void
mt_sigint(void) {}

int
mt_is_parallel(void)
{
  return 0;
}

int
mt_is_thread(void)
{
  return 0;
}

void
pari_mt_init(void)
{
  pari_mt_nbthreads = 1;
}

void
mt_queue_start_lim(struct pari_mt *pt, GEN worker, long lim)
{
  (void) lim;
  mtsingle_queue_start(pt, worker);
}
