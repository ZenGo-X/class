/* Copyright (C) 2013  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#define MT_IS_THREAD              mt_is_thread()
#define MT_SIGINT_BLOCK(block)    do {if (!block) mt_sigint_block();} while(0)
#define MT_SIGINT_UNBLOCK(block)  do {if (!block) mt_sigint_unblock();} while(0)
