#! /bin/sh
. config/version
release=`echo "$pari_release"|sed  's/\./-/g'`
cat << EOT
;--- PARI/GP: NullSoft Installer configuration file
!include "MUI.nsh"
Name "PARI $pari_release_verbose"
!define dll "libpari.dll"
!define PARIver "Pari-$release"
EOT
cat << 'EOT'
;--No need to modify things below --
!define top ".."
!define cfgdir "${top}\config"
AutoCloseWindow false

OutFile "Pari.exe"
InstallDir "$PROGRAMFILES\${PARIver}"
InstallDirRegKey HKLM "Software\${PARIver}" ""

!define MUI_ABORTWARNING

!insertmacro MUI_PAGE_WELCOME
!insertmacro MUI_PAGE_LICENSE "${top}\COPYING"
!insertmacro MUI_PAGE_COMPONENTS
!insertmacro MUI_PAGE_DIRECTORY
!insertmacro MUI_PAGE_INSTFILES
!insertmacro MUI_PAGE_FINISH

!insertmacro MUI_UNPAGE_WELCOME
!insertmacro MUI_UNPAGE_CONFIRM
!insertmacro MUI_UNPAGE_INSTFILES
!insertmacro MUI_UNPAGE_FINISH

!insertmacro MUI_LANGUAGE "English"
;--------------------------------
;Installer Sections

!define uninst "Software\Microsoft\Windows\CurrentVersion\Uninstall\${PARIver}"

Section "pari (required)" SecCopy
  SetOutPath "$INSTDIR"
  File /oname=gp.exe "gp-dyn.exe"
  File /oname=.gprc "${cfgdir}\cygwin-gprc"
  File /oname=postinst "${cfgdir}\cygwin-postinst"
  File "${top}\misc\tex2mail"
  File "${dll}"
  FILE "\cygwin\bin\cygcrypt-0.dll"
  FILE "\cygwin\bin\cygiconv-2.dll"
  FILE "\cygwin\bin\cygintl-8.dll"
  File "\cygwin\bin\cyggmp-3.dll"
  File "\cygwin\bin\cygncursesw-10.dll"
  File "\cygwin\bin\cygreadline7.dll"
  File "\cygwin\bin\cygperl5_10.dll"
  File "\cygwin\bin\cyggcc_s-1.dll"
  File "\cygwin\bin\cygssp-0.dll"
  File "\cygwin\bin\cygwin1.dll"
  File "\cygwin\bin\perl.exe"
  File "\cygwin\bin\sh.exe"
  File "\cygwin\bin\ln.exe"
  SetOutPath "$INSTDIR\terminfo\c"
  File /nonfatal "\cygwin\usr\share\terminfo\c\cygwin"
  SetOutPath "$INSTDIR\terminfo\63"
  File /nonfatal "\cygwin\usr\share\terminfo\63\cygwin"
  SetOutPath "$INSTDIR"
  CreateDirectory "$INSTDIR\..\bin"
  ExecWait 'sh ./postinst'
  Delete "ln.exe"
  Delete "postinst"

  WriteRegStr HKCU "Software\${PARIver}" "" $INSTDIR
  WriteRegStr HKLM ${uninst} "DisplayName" "${PARIver} (remove only)"
  WriteRegStr HKLM ${uninst} "UninstallString" '"$INSTDIR\uninstall.exe"'

  WriteUninstaller "$INSTDIR\Uninstall.exe"
SectionEnd

SectionGroup /e "Data files" SecDATA
Section "Elliptic curves files" SecELL
  SetOutPath "$INSTDIR\data\elldata"
  File "${top}\data\elldata\*"
SectionEnd

Section "Galois files" SecGAL
  SetOutPath "$INSTDIR\data\galdata"
  File "${top}\data\galdata\*"
SectionEnd

Section "Frobenius of elliptic curves files" SecSEA
  SetOutPath "$INSTDIR\data\seadata"
  File "${top}\data\seadata\*"
SectionEnd

Section "Galois polynomial files" SecGPL
  SetOutPath "$INSTDIR\data\galpol"
  File "${top}\data\galpol\*"
SectionEnd
SectionGroupEnd

Section "documentation" SecDOC
  SetOutPath "$INSTDIR"
  File "${top}\doc\gphelp"
  SetOutPath $INSTDIR\doc
  File "${top}\doc\translations"
  File "${top}\doc\*.tex"
  File "${top}\doc\*.pdf"
SectionEnd

Section "examples" SecEX
  SetOutPath "$INSTDIR"
  File "${top}\doc\gphelp"
  SetOutPath $INSTDIR\examples
  File "${top}\examples\EXPLAIN"
  File "${top}\examples\Inputrc"
  File "${top}\examples\*.gp"
  File "${top}\examples\*.c"
  File "${top}\examples\Makefile.cygwin-i686"
SectionEnd

Function .onInstSuccess
  MessageBox MB_OK "Thank you for using PARI/GP! Double-click on 'gp' to start the calculator.$\r$\nTweak $INSTDIR\.gprc to customize GP: colors, script search path, etc."
  ExecShell "open" "$INSTDIR"
FunctionEnd

!define short "$SMPROGRAMS\${PARIver}"

Section "shortcuts" SecSM
  CreateDirectory "${short}"
  CreateShortCut "${short}\gp.lnk" "$INSTDIR\gp.exe" "" "$INSTDIR\gp.exe" 0
  CreateShortCut "${short}\users.lnk" "$INSTDIR\doc\users.pdf" "" "$INSTDIR\doc\users.pdf" 0
  CreateShortCut "${short}\libpari.lnk" "$INSTDIR\doc\libpari.pdf" "" "$INSTDIR\doc\libpari.pdf" 0
  CreateShortCut "${short}\tutorial.lnk" "$INSTDIR\doc\tutorial.pdf" "" "$INSTDIR\doc\tutorial.pdf" 0
  CreateShortCut "${short}\refcard.lnk" "$INSTDIR\doc\refcard.pdf" "" "$INSTDIR\doc\refcard.pdf" 0
  WriteINIStr "${short}\PARI pages.url" "InternetShortcut" "URL" "http://pari.math.u-bordeaux.fr"
  CreateShortCut "${short}\Uninstall.lnk" "$INSTDIR\uninstall.exe" "" "$INSTDIR\uninstall.exe" 0
  CreateShortCut "$DESKTOP\PARI.lnk" "$INSTDIR\gp.exe"
SectionEnd

;--------------------------------
;Descriptions

LangString DESC_SecCopy ${LANG_ENGLISH} "Copy pari files to application folder."
LangString DESC_DOC ${LANG_ENGLISH} "Install documentation and online help."
LangString DESC_EX ${LANG_ENGLISH} "Install sample GP scripts."
LangString DESC_DATA ${LANG_ENGLISH} "Data files pertaining to pari"
LangString DESC_ELL ${LANG_ENGLISH} "Install elliptic curves data files (for ellsearch and ellidentify)."
LangString DESC_GAL ${LANG_ENGLISH} "Install Galois data files (for polgalois in degree > 7)."
LangString DESC_SEA ${LANG_ENGLISH} "Install Modular polynomials (for ellap'SEA implementation)."
LangString DESC_GPL ${LANG_ENGLISH} "Install Galois polynomials data files (for galoisgetpol)."
LangString DESC_SM ${LANG_ENGLISH} "Add PARI shortcuts to Start Menu and desktop."

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${SecCopy} $(DESC_SecCopy)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecDATA} $(DESC_DATA)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecELL} $(DESC_ELL)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecGAL} $(DESC_GAL)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecSEA} $(DESC_SEA)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecGPL} $(DESC_GPL)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecSM} $(DESC_SM)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecDOC} $(DESC_DOC)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecEX} $(DESC_EX)
!insertmacro MUI_FUNCTION_DESCRIPTION_END

;--------------------------------
Section "Uninstall"
  Delete "$INSTDIR\gp.exe"
  Delete "$INSTDIR\.gprc"
  Delete "$INSTDIR\gphelp"
  Delete "$INSTDIR\tex2mail"
  Delete "$INSTDIR\${dll}"
  Delete "$INSTDIR\cygcrypt-0.dll"
  Delete "$INSTDIR\cygiconv-2.dll"
  Delete "$INSTDIR\cygintl-8.dll"
  Delete "$INSTDIR\cyggmp-3.dll"
  Delete "$INSTDIR\cygncursesw-10.dll"
  Delete "$INSTDIR\cygreadline7.dll"
  Delete "$INSTDIR\cygperl5_10.dll"
  Delete "$INSTDIR\cyggcc_s-1.dll"
  Delete "$INSTDIR\cygssp-0.dll"
  Delete "$INSTDIR\cygwin1.dll"
  Delete "$INSTDIR\perl.exe"
  Delete "$INSTDIR\sh.exe"

  Delete "$INSTDIR\Uninstall.exe"
  RMDir /r "$INSTDIR\doc"
  RMDir /r "$INSTDIR\examples"
  RMDir /r "$INSTDIR\data"
  RMDir /r "$INSTDIR\terminfo"

  DeleteRegKey HKLM ${uninst}
  DeleteRegKey /ifempty HKLM "Software\${PARIver}"

  RMDir /r "$SMPROGRAMS\${PARIver}"
  Delete "$DESKTOP\PARI.lnk"
  Delete "$INSTDIR\..\bin\sh"
  RMDir "$INSTDIR\..\bin"
  RMDir "$INSTDIR"
SectionEnd
EOT
