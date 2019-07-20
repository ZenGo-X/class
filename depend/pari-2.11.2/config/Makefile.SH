file=$objdir/Makefile

echo Extracting $file
rm -f $file

# Path to directories
cfg=../$config_dir
data=../$data_dir
doc=../$doc_dir
desc=../$desc_dir
ex=../$examples_dir
misc=../$misc_dir
src=../$src_dir

knone=$src/kernel/none
kern0=$src/kernel/$kernlvl0
kern1=$src/kernel/$kernlvl1

if test -n "$add_funclist"; then
  add_funclist=$src/funclist
fi

#
# File lists
#
kernel="mpker mpinl"
gp=`ls $src_dir/gp/*.c | sed 's,.*/\(.*\)\.c,\1,'`
language=`ls $src_dir/language/*.c | sed 's,.*/\(.*\)\.c,\1,'`
basemath=`ls $src_dir/basemath/*.c | sed 's,.*/\(.*\)\.c,\1,'`
modules=`ls $src_dir/modules/*.c   | sed 's,.*/\(.*\)\.c,\1,'`
mt="mt $thread_engine"

systems=
if test -d "$src_dir/systems/$osname"; then
  systems=`ls $src_dir/systems/$osname/*.c | sed 's,.*/\(.*\)\.c,\1,'`
fi
# remove paridecl: no general recompilation when only changing a prototype
hlist=`ls $src_dir/headers/*.h | grep -v paridecl | grep -v paripriv |\
       sed 's,.*/\(.*\)\.h,\1,'`
# for installation put paridecl back. Remove \n otherwise make will choke.
headerlist="paridecl paripriv `echo $hlist| tr '\n' ' '`"

#Add src/language/parse.c if it is not yet generated
case $language in *parse*);; *) language="$language parse";; esac

# special systems (OS/2 for now)
shortlib_prefix=lib
lib_prefix=lib
dllib_prefix=lib
case "$osname" in
  os2)  shortlib_prefix= # 8.3 filenames
        dllib_prefix= # != lib_prefix to allow gp-dyn link with DLL
	export_lib_create=emximp; export_lib='$(DLLIBPARI)$(_A)'
	export_file=pari.def; export_create="emxexp -u"
	# Actually, the build will fail until the switch to -Zomf
	dlld_ignore=- ;;
  mingw)
    export_file='$(LIBPARI).def';;
  darwin)
    ld_install_name="-Wl,-install_name -Wl,\"$libdir\"/\$(LIBPARI_DYN)";;
esac
case "$osname" in
  mingw|cygwin)
    install_implib="\$(INSTALL_DATA) \$(LIBPARI_SO)\$(_A) \$(LIBDIR)/\$(LIBPARI_SO)\$(_A)";;
  *)
    install_implib="";;
esac

PLOTCFLAGS=
PLOTLIBS=
postconfig=:
plotrunpath=
case "$which_graphic_lib" in
ps|svg|none)
  graph=plot$which_graphic_lib;;
Qt4)
  PLOTCFLAGS="\$(QTINC)"
  PLOTLIBS="\$(QTLIB) $QTLIBS"
  graph=plotQt4;;
fltk)
  PLOTCFLAGS=
  PLOTLIBS="$FLTK_LIBS"
  postconfig='fltk-config --post '
  graph=plotfltk;;
win32)
  PLOTLIBS="-lgdi32"
  graph=plotWin32;;
X11)
  PLOTCFLAGS="$PLOTCFLAGS $X11_INC"
  PLOTLIBS="$PLOTLIBS $X11_LIBS"
  plotrunpath=$X11
  graph=plotX;;
*)
  echo >&2 "### Unrecognized graphic library '$which_graphic_lib'."
  exit 1;;
esac
libgraph="plotport plottty"

KERNOBJS=
for f in $kernel; do
  KERNOBJS="$KERNOBJS $f\$(_O)"
done
OBJS=$KERNOBJS
for f in $basemath $language $modules $systems $mt $libgraph; do
  OBJS="$OBJS $f\$(_O)"
done
OBJSGP=
for f in $gp $graph; do
  OBJSGP="$OBJSGP $f\$(_O)"
done
HEADERS="mpinl.h parimt.h"
for f in $hlist; do
  HEADERS="$HEADERS $src/headers/$f.h";
done

graph="$graph $libgraph"

# runpath
tmp=$runpath
for d in "$plotrunpath" "$gmp" "$readline"; do
  case "$d" in
    ""|yes) ;;
    *) case "$tmp" in
        $d|*$dir_sep$d|*$dir_sep$d$dir_sep*);;
        *) tmp="$tmp$dir_sep$d";;
       esac ;;
  esac
done
RUNPTH_FINAL=
RUNPTH=
if test -n "$runpathprefix"; then
  RUNPTH_FINAL=`$config_dir/ldflags "$LDneedsWl" $runpathprefix"$tmp"`
  RUNPTH=`$config_dir/ldflags "$LDneedsWl" $runpathprefix\\\$\(TOPDIR\)/$objdir$dir_sep"$tmp"`
fi

if test -z "$DLLD"; then
  exec="gp-sta$exe_suff"; static=y
else
  exec="gp-sta$exe_suff gp-dyn$exe_suff"
fi
case "$sizeof_long" in
  4) numbits=32;;
  8) numbits=64;;
esac
dotest="env \"RUNTEST=\$(RUNTEST)\" \"LD_LIBRARY_PATH=.$dir_sep\$\$LD_LIBRARY_PATH\" \$(SHELL) ../src/test/dotest $numbits \"$exe_suff\""
case "$static" in
  n) dft=dyn; libdft=lib-dyn;;
  y) dft=sta; libdft= ;;
esac

CPPFLAGS="-I. -I$src/headers"
if test "$has_dlopen" = builtin; then
  CPPFLAGS="$CPPFLAGS -I$src/systems/$osname"
fi

case "$ln_s" in
  *cp*) ln_objdir=".";;
  *)    ln_objdir="$objdir"
esac

cat > $file << EOT
# Makefile for Pari/GP -- $pretty
#
#  This file was created by Configure. Any change made to it will be
#  lost when Configure is run.
#
TOPDIR="$TOP"

SHELL      = $make_sh
PERL       = $perl
BISON      = bison
AR         = ar
RANLIB     = ranlib

SIZEOF_LONG= $sizeof_long

CC_FLAVOR  =
CC         = $CC \$(CC_FLAVOR)
CPPFLAGS   = $CPPFLAGS
CFLAGS     = $CFLAGS
DLCFLAGS   = $DLCFLAGS
KERNELCFLAGS  = $KERNELCFLAGS
LD_FLAVOR  = \$(CC_FLAVOR)
LD         = $LD \$(LD_FLAVOR)
LDFLAGS    = $LDFLAGS
DLLD_FLAVOR  = \$(LD_FLAVOR)
DLLD       = $DLLD \$(DLLD_FLAVOR)
DLLDFLAGS  = $DLLDFLAGS
EXTRADLLDFLAGS = $EXTRADLLDFLAGS
RUNTEST    = $RUNTEST

# HIGHLY EXPERIMENTAL (only tested with gmp-4.0 on ix86 and Ultra).
# If you've configured and compiled GMP and would like to tune PARI using
# the nice cycle counting functions in GMP, uncomment the 4 lines below
# (correct the first one to the path to your gmp source tree).
#
#GMP     = /some/directory/gmp-4.0/tune
#GMPFLAGS= -DGMP_TIMER
#GMPO1 = \$(GMP)/time.o \$(GMP)/freq.o
#GMPOBJS=\$(GMPO1) \$(GMPO2)
#
#You may need to add a few object files to GMPOBJS. On UltraSparc, uncomment
#the following line
#GMPO2 = \$(GMP)/sparcv9.o

_O	   = .o
_A	   = .a
LIB_PREFIX = $lib_prefix
DLLIB_PREFIX = $dllib_prefix
LIBPARI_BASE = $libpari_base
LIBPARI      = \$(LIB_PREFIX)pari
DLLIBPARI    = \$(DLLIB_PREFIX)pari
LIBPARI_STA  = \$(LIBPARI)\$(_A)
LIBPARI_SO   = \$(DLLIBPARI).$DLSUFFIX
SOLIBPARI    = \$(DLLIB_PREFIX)\$(LIBPARI_BASE).$DLSUFFIX
LIBPARI_DYN   = \$(SOLIBPARI)$sodest
LIBPARI_SONAME= \$(SOLIBPARI)$soname
DL_DFLT_NAME = $DL_DFLT_NAME

LD_INSTALL_NAME  = $ld_install_name

EXPORT_FILE   = $export_file
EXPORT_CREATE = $export_create
EXPORT_LIB    = $export_lib
EXPORT_LIB_CREATE = $export_lib_create
DLLD_IGNORE   = $dlld_ignore
DLLTOOL = $DLLTOOL

RUNPTH       = $RUNPTH
RUNPTH_FINAL = $RUNPTH_FINAL
LDDYN        = $LDDYN
LIBS         = $LIBS
GMPLIBS      = $GMPLIBS
MT_LIBS      = $MT_LIBS
RT_LIBS      = $RT_LIBS
DL_LIBS      = $DL_LIBS
DYN_LIBS     = \$(GMPLIBS) \$(DL_LIBS) \$(RT_LIBS) \$(MT_LIBS) \$(LIBS)
STA_LIBS     = \$(GMPLIBS) \$(DL_LIBS) \$(RT_LIBS) \$(MT_LIBS) \$(LIBS)

RM = rm -f
MV = mv -f
LN = $ln_s
CP_F = cp -f
STRIP      = strip
STRIPFLAGS =

# Change these installation directories to suit your needs.
# DESTDIR is used to install to a false hierachy (to build a Debian package)
INCLUDEDIR= "\$(DESTDIR)$includedir"
LIBDIR    = "\$(DESTDIR)$libdir"
BINDIR    = "\$(DESTDIR)$bindir"
MANDIR    = "\$(DESTDIR)$mandir"
DATADIR   = "\$(DESTDIR)$datadir"
SYSDATADIR= "\$(DESTDIR)$sysdatadir"

EXDIR     = \$(DATADIR)/examples
MISCDIR   = \$(DATADIR)/misc
DOCDIR    = \$(DATADIR)/doc

INSTALL = $cfg/install
INSTALL_PROGRAM = \$(INSTALL)
INSTALL_DATA = \$(INSTALL) -m 644

# Readline
RLINCLUDE = $RLINCLUDE
RLLIBS    = $RLLIBS
# GMP
GMPINCLUDE = $GMPINCLUDE
# Graphic library.
QTMOC      = $QTMOC
QTINC      = $QTINC
QTLIB      = $QTLIB
PLOTCFLAGS = $PLOTCFLAGS
PLOTLIBS   = $PLOTLIBS
CXX        = g++

TOPLDDYN   = "$TOP/$objdir"
# Description system
DESC          = pari.desc
DESC_HELP_GEN = $desc/gen_proto $desc/PARI/822.pm
TMPSUF        = $osname-$arch.tmp

DOTEST=$dotest

OBJS   = $OBJS
OBJSGP = $OBJSGP

TESTS  = $test_extra

.PHONY: gp dft clean

gp: gp-$dft ../gp$suffix$exe_suff $libdft

../gp$suffix$exe_suff: gp-$dft$exe_suff
	-\$(RM) \$@
	-\$(LN) $ln_objdir/gp-$dft$exe_suff \$@

all: $exec lib-sta

lib-sta: \$(LIBPARI_STA)
lib-dyn: \$(LIBPARI_DYN)

\$(LIBPARI_STA): $add_funclist \$(OBJS)
	-\$(RM) \$@
	\$(AR) r \$@ \$(OBJS)
	-\$(RANLIB) \$@

kerntest\$(_O): $src/test/kerntest.c
	\$(CC) -c -I$src/language \$(CPPFLAGS) \$(CFLAGS) -o \$@ $src/test/kerntest.c

dummy\$(_O): $src/test/dummy.c
	\$(CC) -c \$(CPPFLAGS) \$(CFLAGS) -o \$@ $src/test/dummy.c

kerntest: $KERNOBJS dummy\$(_O) kerntest\$(_O)
	\$(CC) \$(CPPFLAGS) \$(CFLAGS) -o \$@ $KERNOBJS dummy\$(_O) kerntest\$(_O) \$(STA_LIBS)

mpinl\$(_O): .headers parilvl0.h parilvl1.h $knone/mpinl.c
	\$(CC) -c \$(CPPFLAGS) \$(CFLAGS) \$(DLCFLAGS) -o mpinl\$(_O) $knone/mpinl.c

test-kernel:: kerntest
	@./kerntest > gp.out;\
	diff -c gp.out $src/test/32/kernel > kern.dif;\
	if test -s kern.dif; then echo "KERNEL BUG"; else echo OK; fi

tune\$(_O): .headers $src/test/tune.c
	\$(CC) \$(GMPFLAGS) \$(CPPFLAGS) \$(CFLAGS) -o \$@ $src/test/tune.c -c

tune: mpinl.h tune-sta
	-\$(RM) tune ../tune
	-\$(LN) tune-sta tune
	-\$(LN) $ln_objdir/tune ../tune

tune-dyn: tune\$(_O) \$(LIBPARI_DYN)
	\$(LD) -L. \$(LDFLAGS) \$(RUNPTH) -o \$@ \$< \$(GMPOBJS) \$(LDDYN) \$(STA_LIBS)
tune-sta: tune\$(_O) \$(LIBPARI_STA)
	\$(LD) \$(LDFLAGS) \$(RUNPTH) -o \$@ \$< \$(GMPOBJS) ./\$(LIBPARI_STA) \$(STA_LIBS)

gp-sta$exe_suff: $add_funclist \$(OBJS) \$(OBJSGP)
	\$(RM) \$@
	\$(LD) -o \$@ \$(LDFLAGS) \$(OBJS) \$(OBJSGP) \$(RUNPTH) \$(RLLIBS) \$(PLOTLIBS) \$(STA_LIBS)
	$postconfig gp-sta$exe_suff

clean_pari_ps::
	@-\$(RM) pari.ps
cleantest:
	\$(RM) *.dif gp.out io-testfile pari.ps
cleanobj:
	-\$(RM) *\$(_O) mpker.c *.s parimt.h mpinl.h parilvl0.h parilvl1.h libpari* $exec kerntest
	-\$(RM) gmon.out
	-\$(RM) *.gcno *.gcda
cleandesc:
	-\$(RM) $desc/\$(DESC) *\$(TMPSUF)
cleantune:
	-\$(RM) tune tune-sta tune\$(_O)

cleanall: cleanobj cleantune cleantest cleandesc

clean: cleanall


# Use this version to avoid problems with NFS and slightly out of synch
# fileserver/host. We are recompiling everything anyway. Not on by default:
# 3s is slower than the whole compilation on our development server :-)
# .headers: $HEADERS
#	@sleep 3; touch \$@
.headers: $HEADERS
	@touch \$@

install-nodata: install-lib-$dft install-include install-bin install-man install-misc install-examples install-cfg

install: install-doc install-nodata install-data

install-include:
	-mkdir -p \$(INCLUDEDIR)/pari
	-for i in paricfg.h mpinl.h parimt.h; do \\
	  \$(INSTALL_DATA) \$\$i \$(INCLUDEDIR)/pari; done
	-for i in $headerlist; do \\
	   \$(INSTALL_DATA) $src/headers/\$\$i.h  \$(INCLUDEDIR)/pari; done
	-\$(RM) \$(INCLUDEDIR)/pari/genpari.h
	-\$(LN) pari.h \$(INCLUDEDIR)/pari/genpari.h

install-bin: install-bin-$dft

install-bin-dyn: gp-dyn$exe_suff install-lib-dyn
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version$exe_suff \$(BINDIR)/gp$exe_suff
	\$(LD) -o \$(BINDIR)/gp-$version$exe_suff -L\$(LIBDIR) \$(LDFLAGS) \$(OBJSGP) \$(RUNPTH_FINAL) \$(LDDYN) \$(RLLIBS) \$(PLOTLIBS) \$(LIBS)
	-\$(STRIP) \$(STRIPFLAGS) \$(BINDIR)/gp-$version$exe_suff
	-cd \$(BINDIR); $postconfig gp-$version$exe_suff
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff

install-bin-sta: gp-sta$exe_suff
	-mkdir -p \$(BINDIR)
	-\$(RM) \$(BINDIR)/gp-$version$exe_suff \$(BINDIR)/gp$exe_suff
	\$(INSTALL_PROGRAM) gp-sta$exe_suff \$(BINDIR)/gp-$version$exe_suff
	-\$(LN) gp-$version$exe_suff \$(BINDIR)/gp$exe_suff
# Can't strip it if we want install() to work on OSF.
#	-\$(STRIP) \$(STRIPFLAGS)  \$(BINDIR)/gp-$version
	-cd \$(BINDIR); $postconfig gp-$version$exe_suff

install-man::
	-mkdir -p \$(MANDIR)
	-\$(RM) \$(MANDIR)/pari.1 \$(MANDIR)/gp.1 \$(MANDIR)/gp-$version.1
	\$(INSTALL_DATA) $doc/gphelp.1 \$(MANDIR)
	\$(INSTALL_DATA) $doc/gp.1 \$(MANDIR)/gp-$version.1
	-\$(LN) gp.1 \$(MANDIR)/pari.1
	-\$(LN) gp-$version.1 \$(MANDIR)/gp.1

install-misc:
	-mkdir -p \$(MISCDIR) \$(BINDIR)
	\$(INSTALL_PROGRAM) $misc/tex2mail \$(BINDIR)
	\$(INSTALL_DATA) $doc/tex2mail.1 \$(MANDIR)
	\$(INSTALL_DATA) $misc/README    \$(MISCDIR)
	\$(INSTALL_DATA) $misc/color.dft \$(MISCDIR)
	\$(INSTALL_DATA) $misc/gpalias   \$(MISCDIR)
	\$(INSTALL_PROGRAM) $misc/gpflog \$(MISCDIR)
	\$(INSTALL_DATA) $misc/gprc.dft  \$(MISCDIR)
	\$(INSTALL_PROGRAM) $misc/xgp    \$(MISCDIR)

install-cfg::
	-mkdir -p \$(SYSDATADIR)
	-\$(INSTALL_DATA) pari.cfg \$(SYSDATADIR)
	-if test -n "$add_funclist"; then\
	   mkdir -p \$(DATADIR)/PARI;\
	   \$(INSTALL_DATA) $desc/PARI/822.pm \$(DATADIR)/PARI;\
	   \$(INSTALL_DATA) $desc/\$(DESC) \$(DATADIR); fi

install-doc: install-docdvi install-doctex

install-doctex:
	-mkdir -p \$(BINDIR) \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/translations \$(DOCDIR)
	-\$(INSTALL_PROGRAM) $doc/gphelp    \$(BINDIR)
	-cd $doc; \$(MAKE) usersch3.tex
	-\$(INSTALL_DATA) $doc/appa.tex     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/appb.tex     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/appd.tex     \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/parimacro.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/pdfmacs.tex  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/develop.tex  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/refcard.tex  \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/tutorial.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/tutorial-mf.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/users.tex    \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch1.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch2.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch3.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch4.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch5.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch6.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch7.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/usersch8.tex \$(DOCDIR)
	-\$(INSTALL_DATA) $doc/paricfg.tex  \$(DOCDIR)

install-docdvi::
	-mkdir -p \$(DOCDIR)
	-cd $doc; \$(MAKE) doc; for f in *.dvi; do \
	  \$(INSTALL_DATA) \$\$f \$(DOCDIR); \
          done

install-docpdf::
	-mkdir -p \$(DOCDIR)
	-cd $doc; \$(MAKE) docpdf; for f in *.pdf; do \
	  \$(INSTALL_DATA) \$\$f \$(DOCDIR); \
          done

install-examples:
	-mkdir -p \$(EXDIR)
	-\$(INSTALL_DATA) $ex/EXPLAIN     \$(EXDIR)
	-\$(INSTALL_DATA) $ex/Inputrc     \$(EXDIR)
	-\$(INSTALL_DATA) $ex/Makefile    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/bench.gp    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/cl.gp       \$(EXDIR)
	-\$(INSTALL_DATA) $ex/classno.gp  \$(EXDIR)
	-\$(INSTALL_DATA) $ex/contfrac.gp \$(EXDIR)
	-\$(INSTALL_DATA) $ex/lucas.gp    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/extgcd.c    \$(EXDIR)
	-\$(INSTALL_DATA) $ex/rho.gp      \$(EXDIR)
	-\$(INSTALL_DATA) $ex/squfof.gp   \$(EXDIR)
	-\$(INSTALL_DATA) $ex/taylor.gp   \$(EXDIR)

install-data:
	-if test -d $data; then cd $data; \
	   for d in \`ls\`; do \
	     mkdir -p \$(DATADIR)/\$\$d && \
	     for f in \`ls \$\$d\`; do \
	       \$(INSTALL_DATA) \$\$d/\$\$f \$(DATADIR)/\$\$d; \
	     done >/dev/null;\
	   done; \
	 fi

install-lib-sta: \$(LIBPARI_STA)
	-mkdir -p \$(LIBDIR)
	-\$(RM) \$(LIBDIR)/\$(LIBPARI_STA)
	\$(INSTALL_DATA) \$(LIBPARI_STA) \$(LIBDIR)/\$(LIBPARI_STA)

install-lib-dyn-base:
	-mkdir -p \$(LIBDIR)
	-\$(RM) \$(LIBDIR)/\$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SONAME) \$(LIBDIR)/\$(LIBPARI_SO)
	\$(DLLD_IGNORE)\$(DLLD) -o \$(LIBDIR)/\$(LIBPARI_DYN) \$(DLLDFLAGS) \$(OBJS) \$(EXTRADLLDFLAGS) \$(DYN_LIBS) \$(EXPORT_FILE) \$(LD_INSTALL_NAME)
	$install_implib

install-lib-dyn-link: install-lib-dyn-base
	-if test "\$(LIBPARI_DYN)" != "\$(LIBDIR)/\$(LIBPARI_SO)"; then \
          \$(LN) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SO); fi
	-if test "\$(LIBPARI_SONAME)" != "\$(LIBPARI_SO)"; then \
	  \$(LN) \$(LIBPARI_DYN) \$(LIBDIR)/\$(LIBPARI_SONAME); fi
install-lib-dyn: \$(LIBPARI_DYN) install-lib-dyn-link

nsis: gp
	-cd $doc; \$(MAKE) docpdf
	makensis pari.nsi

parimt.h: $src/mt/$thread_engine.h
	cat $src/mt/$thread_engine.h > parimt.h

mpinl.h: parilvl0.h parilvl1.h
	cat parilvl0.h parilvl1.h > mpinl.h

bench: $exec clean_pari_ps
	@\$(DOTEST) $test_basic
dobench:: clean_pari_ps
	@\$(DOTEST) $test_basic
test-all: $exec clean_pari_ps
	@\$(DOTEST) \$(TESTS)
dotest-all:: clean_pari_ps
	@\$(DOTEST) \$(TESTS)
dyntest-all: gp-dyn$exe_suff clean_pari_ps
	@env dotestSUF=dyn \$(DOTEST) \$(TESTS)
statest-all: gp-sta$exe_suff clean_pari_ps
	@env dotestSUF=sta \$(DOTEST) \$(TESTS)

dotest-env::
	@export AAA=XXX BBB=YYY; \$(DOTEST) env
EOT

for i in $test_extra $test_extra_out $test_extra_OUT; do
  echo "test-$i: $exec dotest-$i" >>$file
done
for i in $test_extra $test_extra_out; do
  cat >> $file << EOT
dotest-$i::
	@\$(DOTEST) $i
EOT
done

if test "$optimization" = gcov; then
  cat >> $file << EOT

.PHONY: lcov-report lcov-reset
LCOV_TRACE = lcov.info
LCOV_REPORT= lcov-report
LCOV_FLAGS=
GENHTML_FLAGS=
LCOV_TITLE="PARI/GP v$version.$patch lcov report ($status)"

lcov-report:
	\$(RM) \$(LCOV_TRACE)
	rm -rf \$(LCOV_REPORT)
	lcov -c \$(LCOV_FLAGS) -d . -b . -o \$(LCOV_TRACE)
	genhtml \$(GENHTML_FLAGS) --legend -t \$(LCOV_TITLE) -o \$(LCOV_REPORT) \$(LCOV_TRACE)

lcov-reset:
	\$(RM) *.gcda
EOT
fi

if test -n "$exe_suff"; then
cat >> $file << EOT
gp-sta: gp-sta$exe_suff
gp-dyn: gp-dyn$exe_suff
EOT
fi

if test -z "$DLLD"; then
  cat >> $file << EOT

\$(LIBPARI_DYN)::
	@echo "Configure could not find a way to build a shared library on this machine"

EOT
else
  if test -n "$export_file"; then
    case "$osname" in
    os2)
    cat >> $file << EOT

EXPORT_FILE_BASE = $src/systems/os2/pari.def.base
VERSION_VERBOSE = $pari_release_verbose

\$(EXPORT_FILE): \$(OBJS) \$(EXPORT_FILE_BASE)
	cat \$(EXPORT_FILE_BASE) | sed 's/<DLL_BASE>/\$(DLLIBPARI)/' | sed 's/<VENDOR>/pari.math.u-bordeaux.fr\//' | sed 's/<VERSION>/\$(VERSION_VERBOSE)/' | sed 's/<DESCR>/GP\/PARI compiled with \$(CFLAGS)/' > \$@
	\$(EXPORT_CREATE) \$(OBJS) >> \$@

\$(DLLIBPARI)\$(_A): \$(EXPORT_FILE)
	\$(EXPORT_LIB_CREATE) -o \$@ \$(EXPORT_FILE)

EOT
    ;;
    mingw)
    cat >> $file << EOT

\$(EXPORT_FILE): \$(OBJS)
	\$(DLLTOOL) --export-all-symbols -k -z \$@.tmp \$(OBJS)
	echo "LIBRARY \$(LIBPARI)" > \$@ && cat \$@.tmp >> \$@ && rm \$@.tmp
EOT
    ;;
    esac
  fi
  cat >> $file << EOT

gp-dyn$exe_suff: $add_funclist \$(OBJSGP) \$(LIBPARI_DYN) \$(EXPORT_LIB)
	\$(RM) \$@
	\$(LD) -o \$@ -L\$(TOPLDDYN) \$(LDFLAGS) \$(OBJSGP) \$(RUNPTH) \$(RLLIBS) \$(LDDYN) \$(PLOTLIBS) \$(LIBS)
	$postconfig gp-dyn$exe_suff

\$(LIBPARI_DYN): $add_funclist \$(OBJS) \$(EXPORT_FILE)
	-\$(RM) \$(LIBPARI_DYN)
	\$(DLLD_IGNORE)\$(DLLD) -o \$(TOPLDDYN)/\$(LIBPARI_DYN) \$(DLLDFLAGS) \$(OBJS) \$(EXTRADLLDFLAGS) \$(DYN_LIBS) \$(EXPORT_FILE)
	-if test "\$(LIBPARI_DYN)" != "\$(LIBPARI_SO)"; then \
	  \$(RM) \$(LIBPARI_SO);\
	  \$(LN) \$(LIBPARI_DYN) \$(LIBPARI_SO); fi
	-if test "\$(LIBPARI_DYN)" != "\$(LIBPARI_SONAME)"; then \
	  \$(RM) \$(LIBPARI_SONAME);\
	  \$(LN) \$(LIBPARI_DYN) \$(LIBPARI_SONAME); fi
EOT
fi

cat >> $file << EOT
$src/language/parse.h: $src/language/parse.y
	\$(BISON) -d $src/language/parse.y -o $src/language/parse.c
$src/language/parse.c: $src/language/parse.h
	@:
EOT

if test -n "$add_funclist"; then
# files generated using external scripts
HUGELINE="
$src/funclist::
	@-$cfg/genfunclist $src/funclist $desc"
suffix='$$$$-$(TMPSUF)'
list="funclist init default gp_init"
for name in $list; do
  case $name in
  funclist)
    target="$desc/\$(DESC)"
    depend="$src/funclist $desc/merge_822 $desc/PARI/822.pm"
    script="merge_822 ../$src/funclist"
  ;;
  init)
    target=$src/language/init.h
    depend="$desc/\$(DESC) \$(DESC_HELP_GEN)"
    script="gen_proto basic \$(DESC)"
  ;;
  default)
    target=$src/language/default.h
    depend="$desc/\$(DESC) \$(DESC_HELP_GEN)"
    script="gen_proto default \$(DESC)"
  ;;
  gp_init)
    target=$src/gp/gp_init.h
    depend="$desc/\$(DESC) \$(DESC_HELP_GEN)"
    script="gen_proto gp \$(DESC)"
  ;;
  esac
HUGELINE="$HUGELINE
$target: $depend
	f=$name-$suffix; (cd $desc && \$(PERL) $script > \$\$f) && mv $desc/\$\$f \$@"
done
echo "$HUGELINE" >> $file

fi

# Level 0
f=src/kernel/$kernlvl0/MakeLVL0.SH
if test -s $f; then
  . $f
else
  cat >> $file <<EOT
L0MODS=$kern0/asm0.h $knone/addll.h $knone/mulll.h $knone/bfffo.h $knone/divll.h
parilvl0.h: \$(L0MODS)
	$cfg/genkernel $src $kern0/asm0.h > parilvl0.h
EOT
fi

if test -f "$TOP/.git/index"; then
  vcfile="../.git/index"
  cat >> $file <<EOT
paricfg.h: $vcfile $cfg/version
	-sh $cfg/setversion
EOT
fi

# Level 1
f=src/kernel/$kernlvl1/MakeLVL1.SH
if test -s $f; then . $f; fi

ANAL_H=$src/language/anal.h
RECT_H=$src/graph/rect.h
HUGELINE=
for dir in basemath modules language gp graph systems mt; do
  eval list='$'$dir
  case "$dir" in
    systems)  SRC=$src/$dir/$osname;;
    *)        SRC=$src/$dir;;
  esac
  for f in $list; do

  source="$SRC/$f.c"
  f=`basename $f`
  depend=
  cflags="\$(CPPFLAGS)"
  compile='$(CC)'
  case "$f" in
  gp)
    cflags="$cflags -I$src/language -DDL_DFLT_NAME=\$(DL_DFLT_NAME)"
    depend="$src/gp/gp.h $src/gp/gp_init.h"
    ;;
  gp_rl|texmacs)
    cflags="$cflags -I$src/language \$(RLINCLUDE)"
    depend="$src/gp/gp.h"
    ;;
  paricfg)
    depend="./paricfg.h"
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  plotport)
    cflags="$cflags \$(DLCFLAGS)"
    depend="$RECT_H"
    ;;
  plotsvg|plotps)
    ;;
  plotQt4)
    cflags="$cflags \$(PLOTCFLAGS)"
    depend="$RECT_H"
    compile="\$(QTMOC) \$(PLOTCFLAGS) -o plotQt4.moc.cpp $src/graph/plotQt4.c && \$(CXX)"
    ;;
  plotfltk)
    cflags="$cflags \$(PLOTCFLAGS)"
    depend="$RECT_H"
    compile="\$(CXX)"
    ;;
  plotX)
    cflags="$cflags \$(PLOTCFLAGS)"
    depend="$RECT_H"
    ;;
  es)
    cflags="$cflags \$(DLCFLAGS)"
    depend="$ANAL_H"
    ;;
  whatnow)
    depend="$src/gp/whatnow.h"
    ;;
  init)
    depend="$ANAL_H $src/language/init.h $src/language/default.h"
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  anal)
    depend="$ANAL_H $src/language/parse.h"
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  parse)
    depend="$ANAL_H $src/language/parse.h $src/language/parsec.h $src/language/tree.h"
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  compile)
    depend="$ANAL_H $src/language/tree.h $src/language/opcode.h"
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  eval)
    depend="$ANAL_H $src/language/opcode.h"
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  ratpoints)
    cflags="$cflags \$(DLCFLAGS) \$(KERNELCFLAGS)"
    ;;
  *)
    cflags="$cflags \$(DLCFLAGS)"
    ;;
  esac
cflags="$cflags \$(CFLAGS)"
HUGELINE="$HUGELINE
$f\$(_O): .headers $depend $source
	$compile -c $cflags -o $f\$(_O) $source"
  done
done
# avoid execing too many "cat". MS-DOS can't handle it
echo "$HUGELINE" >> $file
