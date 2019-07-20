file=Makefile
echo "Extracting $file"
rm -f $file

dosversion=`echo $version|sed -e 's/\.//g'`
dosversion="_$dosversion$patch"
__status__=$status
case "$status" in
  development*) __status__='snapshot';;
esac

cat > $file << EOT
# This file was created by Configure. All changes made will be lost
# next time Configure is run.
#
SHELL = $make_sh
VERS = pari-$version.$patch $__status__
TAG=release-$VersionMajor-$VersionMinor-$patch

dft target::
	@echo "Main targets: we suggest 'make all', then 'make install' as root"
	@echo "    all                    Compilation + Documentation"
	@echo "    gp                     Compilation"
	@echo "    bench                  Compilation + Quick test"
	@echo "    dobench                Quick test only"
	@echo "    doc                    Documentation only"
	@echo "    install                Installation"
	@echo "    clean, cleantest       Clean up"
	@echo "For pari maintainers:"
	@echo "    dbg                    Compile gp binary suitable for debugging"
	@echo "    prf                    Compile gp binary suitable for profiling"
	@echo "    gcov                   Compile gp binary for test coverage reporting"
	@echo "    alpha, beta, release   Tarfile for official source distribution"
	@echo "    snapshot, distrib      Tarfile for source snapshot"
	@echo "    nsis                   Create a NSIS installer for win32"
	@echo "    ctags                  Generate VI/VIM tags file in ./src"
	@echo "    etags                  Generate Emacs  tags file in ./src"
	@echo "    tune                   Generate tuning utility"
	@echo "    test-all               Thorough regression tests (slow)"

all::
	@\$(MAKE) gp
	@-cd doc && \$(MAKE) doc

gp bench test-kernel test-all install cleanall cleanobj cleantest nsis install-bin install-doc install-docpdf install-nodata install-data install-lib-sta install-bin-sta dobench dyntest-all statest-all tune $top_test_extra $top_dotest_extra::
	@dir=\`config/objdir\`; echo "Making \$@ in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) \$@

dbg gp.dbg::
	@dir=\`config/objdir\`.dbg; echo "Making gp in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -g first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) gp

prf gp.prf::
	@dir=\`config/objdir\`.prf; echo "Making gp in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -pg first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) gp

gcov gp.gcov::
	@dir=\`config/objdir\`.gcov; echo "Making gp in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -gcov first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) gp

doc docps docpdf gpman cleandoc::
	cd doc && \$(MAKE) \$@

clean:: cleandoc cleanall

clean.dbg::
	@dir=\`config/objdir\`.dbg; echo "Making clean in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Nothing to be done"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) clean

clean.prf::
	@dir=\`config/objdir\`.prf; echo "Making clean in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Nothing to be done"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) clean

clean.gcov::
	@dir=\`config/objdir\`.gcov; echo "Making clean in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Nothing to be done"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) clean

bench.dbg::
	@dir=\`config/objdir\`.dbg; echo "Making bench in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -g first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) bench

bench.prf::
	@dir=\`config/objdir\`.prf; echo "Making bench in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -pg first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) bench

bench.gcov::
	@dir=\`config/objdir\`.gcov; echo "Making bench in \$\$dir";\\
	 if test ! -d \$\$dir; then echo "Please run Configure -gcov first!"; exit 1; fi;\\
	cd \$\$dir && \$(MAKE) bench

distrib:
	$config_dir/settar \$(VERS) $__status__

setdoc:
	cd doc && \$(MAKE) usersch3.tex
alpha: setdoc
	$config_dir/settar \$(VERS) alpha
beta: setdoc
	$config_dir/settar \$(VERS) beta
release: setdoc
	$config_dir/settar \$(VERS) released
snapshot: setdoc
	$config_dir/settar \$(VERS) snapshot

dosdistrib: gpman
	-zip -kr GPB${dosversion}.ZIP GP.EXE README README.DOS ../EMX/README.DOC ../RSX/README.TXT
	-zip -k GPD${dosversion}.ZIP doc/*.tex doc/gphelp doc/gp.man examples misc/gprc* misc/gpalias

etags:
	config/make_tags --emacs "$TOP/src"

ctags:
	config/make_tags --vi "$TOP/src"

checkspaces:
	config/checkspaces

EOT
