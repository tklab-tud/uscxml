ifeq ($(OS),Windows_NT)
    HOST_OS := Windows
	TARGET = .exe
  else
    HOST_OS := $(shell uname)
endif

all: inv-generator$(TARGET)

CC    = gcc
CXX   = g++
LD    = gcc
CFLAGS=-I$(IDIR) 

IDIR = include
SDIR = src
ODIR=obj

ifeq ($(OS),Windows_NT)
    HOST_OS := Windows
  else
    HOST_OS := $(shell uname)
endif

### Verbosity control. Use  make V=1  to get verbose builds.

ifeq ($(V),1)
  TRACE_CC =
  TRACE_LD =
  TRACE_AR =
  TRACE_AS =
  Q=
else
  TRACE_CC = @echo "  CC       " $<
  TRACE_LD = @echo "  LD       " $@
  TRACE_AR = @echo "  AR       " $@
  TRACE_AS = @echo "  AS       " $<
  Q=@
endif

# Provide way to create $(OBJECTDIR) if it has been removed by make clean
$(ODIR):
	mkdir $@

_DEPS =Common.h Header_Parser.h Source_Parser.h Uscxml_Contiki_Invoker_Header.h Uscxml_Contiki_Invoker_Source.h
DEPS = $(patsubst %,$(IDIR)/%,$(_DEPS))


_SRC =Common.cpp Header_Parser.cpp Source_Parser.cpp Uscxml_Contiki_Invoker_Header.cpp Uscxml_Contiki_Invoker_Source.cpp Generator.cpp
_OBJ = ${patsubst %.cpp,%.o,$(_SRC)}
OBJ = $(patsubst %,$(ODIR)/%,$(_OBJ))

vpath %.cpp $(SDIR)

ifeq ($(HOST_OS),Windows)
include makefile.win32
endif

ifndef CUSTOM_RULE_CPP_TO_OBJECTDIR_O
$(ODIR)/%.o: %.cpp $(DEPS)| $(ODIR)
	$(TRACE_CC)
	$(Q) $(CXX) $(CFLAGS) -std=c++11 -c $< -o $@
endif

ifndef CUSTOM_RULE_LINK
inv-generator$(TARGET): $(OBJ)
	$(TRACE_LD)
	$(Q) $(CXX) $(LDFLAGS) $(OBJ) -o $@
endif
	
.PHONY: clean

clean:
	rm -f $(ODIR)/*.o inv-generator$(TARGET)
