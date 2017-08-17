CONTIKI_PROJECT = dining_philosopher
all: $(CONTIKI_PROJECT)
USCXML = 1
#----IMPORTANT CONFIGURATION-----------------------------------------------------------------------------------
include configure_before_make
#----IMPORTANT CONFIGURATION END-----------------------------------------------------------------------------------

ifdef VCINSTALLDIR
  ifeq ($(BUILD_TYPE),debug)
    BUILD_TYPE_FLAG = /MDd
  else
    ifeq ($(BUILD_TYPE),release)
      BUILD_TYPE_FLAG = /MD	  
	else
	  ${error The BUILD_TYPE does not exist (maybe it was misspelled?)}	    
	endif #$(BUILD_TYPE),release
  endif #$(BUILD_TYPE),debug
endif #VCINSTALLDIR

#----Custom invokers for uscxml-contiki application--------------------------------------------------------------
#PLEASE READ Adding_invoker.txt to include additional invoker to this contiki application.

#Makefile.invokers contains additional configuration required to add invokers
ifdef WITH_INVOKERS
include invokers/Makefile.invokers 
endif

#----Custom invokers for uscxml-contiki APP End------------------------------------------------------------------

#----USCXML Source files addition--------------------------------------------------------------------------------
#Added contiki interface sourcefile here rest all uscxml related sourcefile are added in Makefile.project.

include Makefile.project

#----USCXML Source files addition End--------------------------------------------------------------------------------


ifdef VCINSTALLDIR

  ifeq ($(BUILD_TYPE),debug)
    #DEBUG_DIRECTIVE = "_DEBUG"
	DEBUG_DIRECTIVE = "NDEBUG"	
  else
    DEBUG_DIRECTIVE = "NDEBUG"
  endif #($(BUILD_TYPE),debug)

VCFLAGS += /D "WIN32" /D "_WINDOWS" /D $(DEBUG_DIRECTIVE) /D "NO_XERCESC" /D "FEATS_ON_CMD" /D "WITH_DM_PROMELA" /D "_SCL_SECURE_NO_WARNINGS" /D "_CRT_SECURE_NO_WARNINGS" /D "CURL_STATICLIB" /D "USCXML_STATIC" 
else

CFLAGS += -DNO_XERCESC -DFEATS_ON_CMD -DWITH_DM_PROMELA -DUSCXML_STATIC -DCURL_STATICLIB  -DNDEBUG

endif #VCINSTALLDIR

#For contiki makefile verbose build
V = 1 

ifdef VCINSTALLDIR
#Disabling IPv6 and enabling IPv4
CONTIKI_WITH_IPV4=1
CONTIKI_WITH_IPV6=0
CONTIKI_WITH_RPL=0

endif #VCINSTALLDIR

include $(CONTIKI)/Makefile_uscxml.include
