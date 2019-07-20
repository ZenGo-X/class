#! /bin/sh
. config/version
bitsize=$1
release=`echo "$pari_release"|sed  's/\./-/g'`
cat << EOT
;--- PARI/GP: NullSoft Installer configuration file
!include "MUI.nsh"
Name "PARI $pari_release_verbose (${bitsize}bit)"
!define dll "libpari.dll"
!define PARIver "Pari$bitsize-$release"
EOT
cat << 'EOT'
!define top ".."
!define tree "..\mingw"
AutoCloseWindow false

OutFile "..\${PARIver}.exe"
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
  File "${tree}\bin\gp.exe"
  File "${tree}\bin\${dll}"
  File /oname=gphelp.pl "${tree}\bin\gphelp"
  File /oname=gprc.txt "${tree}\gprc.mingw"

  WriteRegStr HKCU "Software\${PARIver}" "" $INSTDIR
  WriteRegStr HKLM ${uninst} "DisplayName" "${PARIver} (remove only)"
  WriteRegStr HKLM ${uninst} "UninstallString" '"$INSTDIR\uninstall.exe"'

  WriteUninstaller "$INSTDIR\Uninstall.exe"
SectionEnd

Section "Data files" SecGAL
  SetOutPath "$INSTDIR"
  File /r "${tree}\data"
SectionEnd

Section "documentation" SecDOC
  CreateDirectory "$INSTDIR\etc"
  SetOutPath "$INSTDIR"
  File /r "${tree}\share\pari\doc"
  File /r "${tree}\perl"
  File /r "${tree}\share\pari\examples"
  File /oname=gprc_dft.txt "${tree}\gprc.dft"
SectionEnd

Section "Development files" SecDEV
  CreateDirectory "$INSTDIR\include"
  CreateDirectory "$INSTDIR\lib"
  SetOutPath "$INSTDIR"
  File /r "${tree}\lib"
  File /r "${tree}\include"
SectionEnd

Function .onInstSuccess
  MessageBox MB_OK "Thank you for using PARI/GP! Double-click on 'gp' to start the calculator.$\r$\n"
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
LangString DESC_GAL ${LANG_ENGLISH} "Install Pari package files."
LangString DESC_DEV ${LANG_ENGLISH} "Add libpari development files."
LangString DESC_SM ${LANG_ENGLISH} "Add PARI shortcuts to Start Menu and desktop."

!insertmacro MUI_FUNCTION_DESCRIPTION_BEGIN
  !insertmacro MUI_DESCRIPTION_TEXT ${SecCopy} $(DESC_SecCopy)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecGAL} $(DESC_GAL)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecSM} $(DESC_SM)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecDOC} $(DESC_DOC)
  !insertmacro MUI_DESCRIPTION_TEXT ${SecDEV} $(DESC_DEV)
!insertmacro MUI_FUNCTION_DESCRIPTION_END

;--------------------------------
Section "Uninstall"
  Delete "$INSTDIR\gp.exe"
  Delete "$INSTDIR\gphelp.pl"
  Delete "$INSTDIR\gprc_dft.txt"
  Delete "$INSTDIR\${dll}"

  RMDir /r "$INSTDIR\perl"
  RMDir /r "$INSTDIR\etc"
  RMDir /r "$INSTDIR\doc"
  RMDir /r "$INSTDIR\examples"
  RMDir /r "$INSTDIR\data"
  RMDir /r "$INSTDIR\include"
  RMDir /r "$INSTDIR\lib"
  Delete "$INSTDIR\Uninstall.exe"

  DeleteRegKey HKLM ${uninst}
  DeleteRegKey /ifempty HKLM "Software\${PARIver}"

  RMDir /r "$SMPROGRAMS\${PARIver}"
  Delete "$DESKTOP\PARI.lnk"
  RMDir "$INSTDIR"
SectionEnd
EOT
