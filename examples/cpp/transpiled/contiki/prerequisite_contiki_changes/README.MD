========================================================================
   
                    Contiki Build Changes. 
    
========================================================================

Following are one time Contiki build changes that are mandatory for building SCXML based contiki applications using uscxml interpreter and PROMELA datamodel.

This directory path contains 4 files.

1) Makefile_uscxml.include : 
Copy this file in directory 'YOUR_CONTIKI_DIR'. This is main contiki dir where file 'makefile.include'  is present.

2) contiki-conf.h : 
Copy and replace this file in the directory 'YOUR_CONTIKI_DIR'/platform/win32.

3) Makefile.uscxmlrules-native : 
Copy this file in the directory 'YOUR_CONTIKI_DIR'/platform/native.

4) Makefile.uscxmlrules-win32 : 
Copy this file in directory  'YOUR_CONTIKI_DIR'/platform/win32.

(P.S - Changes 2) and 4) are not required if building for TARGET=native only. Similarly change 3) is optional if only building for TARGET=win32.)