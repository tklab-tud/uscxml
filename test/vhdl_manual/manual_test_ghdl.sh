#!/bin/bash
#
# https://sourceforge.net/p/umhdl/wiki/Installation%20-%20Linux/
# https://linux.die.net/man/1/ghdl
# 

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )/"

# TODO generate dirs with CMAKE as absolut path
SCXML_BIN=$DIR"../../build/bin/"
SCXML_TEST=$DIR"../"

SIM_DIR=$DIR"../../build/simulation/"
VHDL_OUT=${SIM_DIR}vhd/
SIM_LIB_DIR=${SIM_DIR}scxml/
VHDL_TB_NAME=tb

SIMULATION_CMD="${INSTALL_DIR}vsim work.tb -do debug.do"

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
ghdl --clean
ghdl -a -Wa,--32 ${VHDL_OUT}dut.vhd

if [ $? -eq 0 ] ; then
    echo "syntax check ok."
else
    echo "syntax check FAILED."
    exit -1
fi

ghdl -e -Wa,--32 -Wl,-m32 ${VHDL_TB_NAME}

if [ $? -eq 0 ] ; then
    echo "compilation done."
else
    echo "compilation FAILED"
    exit -1
fi

# start simulator
ghdl -r tb --stop-time=10ms --vcd=tb.vcd
