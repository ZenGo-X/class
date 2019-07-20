/* Copyright (C) 2009  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Written by Vasili Burdo */

#include <windows.h>
#include <stdio.h>

char* win32_datadir(void)
{
  char datadir[1024];
  char* slash;
  GetModuleFileNameA(0, datadir, sizeof(datadir) );
  slash = strrchr(datadir, '\\');
  if( slash ) *(slash+1) = 0;
  strcat(datadir, "data");
  return strdup(datadir);
}
