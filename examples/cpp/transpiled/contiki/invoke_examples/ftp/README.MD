========================================================================
    MAKEFILE PROJECT : uscxml-contiki Project Overview
========================================================================

Please follow below steps exactly to build contiki specific uscxml application.
(P.S : If building for TARGET = win32, please use visual studio command prompt.)

1) Edit Makefile in this directory and add correct path for uscxml, uscxml build path, contiki build path. 
2) Please select if you want to build this application with invoker or without invoker by setting/commenting WITH_INVOKERS variable present in Makefile (do it by - WITH_INVOKERS = 1 or #WITH_INVOKERS = 1)
3) If WITH_INVOKERS is set (i.e WITH_INVOKERS = 1) then follow invokers/invokers_readme.txt before continuing with further steps.



/////////////////////////////////////////////////////////////////////////////
