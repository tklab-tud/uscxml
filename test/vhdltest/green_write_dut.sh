#!/bin/bash

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )/"

SCXML_BIN=$DIR"../../build/bin/"
SCXML_TEST=$DIR"../"

SIM_DIR=$DIR"../../build/simulation/"
#INSTALL_DIR=/home/juehv/altera/13.1/modelsim_ase/bin/
INSTALL_DIR=""
VHDL_OUT=${SIM_DIR}vhd/
SIM_LIB_DIR=${SIM_DIR}scxml/

LIB_CREATE_CMD="${INSTALL_DIR}vlib $SIM_LIB_DIR"
LIB_MAP_CMD="${INSTALL_DIR}vmap work $SIM_LIB_DIR"
COMPILE_CMD="${INSTALL_DIR}vcom ${VHDL_OUT}dut.vhd"
#SIMULATION_CMD="${INSTALL_DIR}vsim -c scxml_lib.testbench -do automation.tcl"
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
cp ./debug.do $SIM_DIR
cp ./automation.tcl $SIM_DIR
#cp ./modelsim.ini $SIM_DIR

# Write file
cd $DIR
#${SCXML_BIN}uscxml-transform -t vhdl -i ${SCXML_TEST}/w3c/ecma/${TEST_NUMBER} -o ${VHDL_OUT}dut.vhd
${SCXML_BIN}uscxml-transform -t vhdl -i /home/juehv/Desktop/green.scxml -o ${VHDL_OUT}dut.vhd
#echo "$(cat ${VHDL_OUT}dut.vhd)"
echo "${VHDL_OUT}dut.vhd written"
TMP_RESULT="$(tail -n 1 ${VHDL_OUT}dut.vhd)"

if [ "$TMP_RESULT" == "ERROR" ] ; then
  echo "Error while generating VHDL"
  exit -1
fi

# map librarys
cd ${SIM_DIR}
$LIB_CREATE_CMD
$LIB_MAP_CMD
echo "Library mapped"

# compile stuff
cd ${SIM_DIR}
${COMPILE_CMD}

if [ $? -eq 0 ] ; then
    echo "compilation done."
else
    echo "compilation failed"
    exit -1
fi

# start simulator
${SIMULATION_CMD}
