/* Copyright (C) 2009  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

const char* win32_basedir(void);
char* win32_datadir(void);
void win32_ansi_fputs(const char* s, void* f);
int win32_terminal_width(void);
int win32_terminal_height(void);
void win32_set_codepage(void);
void win32_set_pdf_viewer(void);
void win32_alarm(unsigned int s);
long win32_timer(void);
long win32_nbthreads(void);
