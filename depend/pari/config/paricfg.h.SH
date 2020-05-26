file="$objdir/paricfg.h"

echo Extracting $file
rm -f $file

case "$optimization" in
  full) ;;
  *) debuginfo=" -- $optimization";;
esac

if test -n "$perl"; then
  case "$osname" in
    os2|mingw) gphelp="perl -S gphelp -detex" ;;
    *) gphelp="\\\"$bindir/gphelp\\\"" ;;
  esac
fi

has_stack_check=
if test "$osname" = "os2" -o "$has_getrlimit" = "yes"; then
  has_stack_check=yes;
fi

cat > $file << EOT
/*  This file was created by Configure. Any change made to it will be lost
 *  next time Configure is run. */
#ifndef __PARICFG_H__
#define __PARICFG_H__
EOT

cat >> $file << EOT
#define UNIX
#define GPHELP "$gphelp"
#define GPDATADIR "$datadir"
#define SHELL_Q '\\$shell_q'

#define PARIVERSION "GP/PARI CALCULATOR Version ${version}.${patch} (${status})"
#define PARIINFO "${pretty}${debuginfo}"
#define PARI_VERSION_CODE ${version_code}
#define PARI_VERSION(a,b,c) (((a) << 16) + ((b) << 8) + (c))
#define PARI_VERSION_SHIFT 8
#define PARI_VCSVERSION "${vcsversion}"
#define PARI_MT_ENGINE "${thread_engine}"

#define PARI_DOUBLE_FORMAT ${doubleformat}
EOT

if test -n "$__gnuc__"; then
  echo "#define GCC_VERSION \"$__gnuc__\"" >> $file
fi

case $asmarch in
  none) echo '#define __HAS_NO_ASM__' >> $file;;
  hppa) echo '#define __HPPA__' >> $file;;
esac

if test -n "$ASMINLINE"; then
  echo '#define ASMINLINE' >> $file
fi

if test -n "$gzip"; then
  cat >> $file << EOT

/*  Location of GNU gzip program (enables reading of .Z and .gz files). */
#define GNUZCAT
#define ZCAT "$gzip -dc"

EOT
else if test -n "$zcat"; then
  cat >> $file << EOT

/*  Location of zcat program (enables reading of .Z files). */
#define ZCAT "$zcat"

EOT
  fi
fi

if test -n "$gp_mime_open"; then
  cat >> $file << EOT

#define GP_MIME_OPEN "$gp_mime_open"

EOT
fi

if test "$osname" = "mingw"; then
cat >> $file << EOT

#undef UNIX
#define GNUZCAT
#undef ZCAT
#define ZCAT "gzip.exe -dc"

EOT
fi

if test -n "$readline"; then
  cat >> $file <<EOT
#define READLINE "$readline_version"
EOT
fi

case "$sizeof_long" in
8) echo '#define LONG_IS_64BIT' >> $file;;
esac

case $has_sse2 in
yes) echo '#define HAS_SSE2' >> $file;;
esac

case "$has_exp2" in
yes) echo '#define HAS_EXP2' >> $file;;
esac
case "$has_log2" in
yes) echo '#define HAS_LOG2' >> $file;;
esac
case "$has_isatty" in
yes) echo '#define HAS_ISATTY' >> $file;;
esac
case "$has_alarm" in
yes) echo '#define HAS_ALARM' >> $file;;
esac
case "$has_system" in
yes) echo '#define HAS_SYSTEM' >> $file;;
esac


case "$has_clock_gettime" in
yes) echo '#define USE_CLOCK_GETTIME 1' >> $file;;
  *) case "$has_getrusage" in
     yes) echo '#define USE_GETRUSAGE 1' >> $file;;
       *) case "$has_times" in
          yes) echo '#define USE_TIMES 1' >> $file;;
            *) case "$has_ftime" in
               yes) echo '#define USE_FTIME 1' >> $file;;
               esac;;
          esac;;
     esac;;
esac

case "$has_gettimeofday" in
yes) echo '#define USE_GETTIMEOFDAY 1' >> $file;;
  *) case "$has_ftimeforwalltime" in
     yes) echo '#define USE_FTIMEFORWALLTIME 1' >> $file;;
     esac;;
esac

case $has_sigaction in
yes) echo '#define HAS_SIGACTION' >> $file;;
esac

case $has_waitpid in
yes) echo '#define HAS_WAITPID' >> $file;;
esac

case $has_getenv in
yes) echo '#define HAS_GETENV' >> $file;;
esac

case $has_setsid in
yes) echo '#define HAS_SETSID' >> $file;;
esac

case $has_dlopen in
yes|builtin) echo '#define HAS_DLOPEN' >> $file;;
esac

case $has_stack_check in
yes) echo '#define STACK_CHECK' >> $file;;
esac

case $has_vsnprintf in
yes) echo '#define HAS_VSNPRINTF' >> $file;;
esac

case $has_TIOCGWINSZ in
yes) echo '#define HAS_TIOCGWINSZ' >> $file;;
esac

case $has_strftime in
yes) echo '#define HAS_STRFTIME' >> $file;;
esac

case $has_opendir in
yes) echo '#define HAS_OPENDIR' >> $file;;
esac

case $has_stat in
yes) echo '#define HAS_STAT' >> $file;;
esac

case $has_mmap in
yes) echo '#define HAS_MMAP' >> $file;;
esac

case $enable_tls in
yes) echo '#define ENABLE_TLS' >> $file;;
esac

echo '#endif' >> $file
