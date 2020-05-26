/* Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

BEGINEXTERN

typedef enum {Gvoid, Gsmall, Gvec, Gvar, Ggen, Gclosure, Gusmall} Gtype;

typedef enum {OCpushlong='A',OCpushgnil,OCpushgen,OCpushreal,OCpushstoi,OCpushvar,
              OCpop,
              OCstoi,OCitos,OCtostr,OCvarn,OCcopy,OCcopyifclone,
              OCprecreal,OCprecdl,
              OCvec,OCmat,OCcol,
              OCstackgen,
              OCcompo1,OCcompo2,OCcompoC,OCcompoL,
              OCpushptr,OCendptr,
              OCcompo1ptr,OCcompo2ptr,OCcompoCptr,OCcompoLptr,
              OCcalllong,OCcallgen,OCcallgen2,OCcallint,OCcallvoid,OCcalluser,
              OCnewframe,OCsaveframe,
              OCpushdyn,OCstoredyn,OCnewptrdyn,OCsimpleptrdyn,
              OCpushlex,OCstorelex,OCnewptrlex,OCsimpleptrlex,
              OCgetargs,OCdefaultarg,OClocalvar,OClocalvar0,
              OCcheckargs,OCcheckargs0,OCdefaultgen,OCdefaultlong,
              OCavma,OCgerepile,
              OCcowvardyn,OCcowvarlex,
              OCdup,OCstoreptr,OCcheckuserargs,
              OCitou,OCutoi,OCdefaultulong,
              OCbitprecreal='@'} op_code;

ENDEXTERN
