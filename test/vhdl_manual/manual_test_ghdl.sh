#!/bin/bash
#
# https://sourceforge.net/p/umhdl/wiki/Installation%20-%20Linux/
# https://linux.die.net/man/1/ghdl
# 
# needs a up-to-date verson of ghdl (at least 0.32)
# https://github.com/tgingold/ghdl
# ./configure --with-llvm-config=/usr/bin/llvm-config --prefix=/opt/ghdl
# sudo mkdir /opt/ghdl
# make
# sudo make install
# OR install from https://github.com/tgingold/ghdl/releases/tag/v0.33

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )/"

# TODO generate dirs with CMAKE as absolut path
SCXML_BIN=$DIR"../../build/bin/"
SCXML_TEST=$DIR"../"

SIM_DIR=$DIR"../../build/simulation/"
VHDL_OUT=${SIM_DIR}vhd/
SIM_LIB_DIR=${SIM_DIR}scxml/
VHDL_TB_NAME=tb

#GHDL=/opt/ghdl/bin/ghdl
GHDL=ghdl

# get arguments
TEST_NUMBER="test144.scxml"
if [ "$1" != "" ] ; then
  TEST_NUMBER="$1"
fi

# init simulation dir
rm -rf $SIM_DIR
mkdir -p $SIM_DIR
mkdir -p $VHDL_OUT

# Write file
cd $DIR
${SCXML_BIN}uscxml-transform -t vhdl -i ${SCXML_TEST}/w3c/ecma/${TEST_NUMBER} -o ${VHDL_OUT}dut.vhd
#echo "$(cat ${VHDL_OUT}dut.vhd)"
echo "${VHDL_OUT}dut.vhd written"
TMP_RESULT="$(tail -n 1 ${VHDL_OUT}dut.vhd)"

if [ "$TMP_RESULT" == "ERROR" ] ; then
  echo "Error while generating VHDL"
  exit -1
fi

# compile stuff
cd ${SIM_DIR}
${GHDL} --clean
${GHDL} -a --std=08 ${VHDL_OUT}dut.vhd
#${GHDL} -a -Wa,--32 ${VHDL_OUT}dut.vhd

if [ $? -eq 0 ] ; then
    echo "syntax check ok."
else
    echo "syntax check FAILED."
    exit -1
fi

${GHDL} -e --std=08 ${VHDL_TB_NAME}
#${GHDL} -e -Wa,--32 -Wl,-m32 ${VHDL_TB_NAME}

if [ $? -eq 0 ] ; then
    echo "compilation done."
else
    echo "compilation FAILED"
    exit -1
fi

# start simulator
${GHDL} -r tb --vcd=tb.vcd
#${GHDL} -r tb --stop-time=10ms --vcd=tb.vcd
