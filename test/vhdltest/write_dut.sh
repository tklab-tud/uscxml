#!/bin/bash
SCXML_BIN=/home/juehv/git/uscxml/build/bin/
SCXML_TEST=/home/juehv/git/uscxml/test/

SIM_DIR=/home/juehv/modelsim/automated_test/
INSTALL_DIR=/home/juehv/altera/13.1/modelsim_ase/bin/
VHDL_OUT=${SIM_DIR}vhd/

COMPILE_CMD="${INSTALL_DIR}vcom ${VHDL_OUT}dut.vhd ${VHDL_OUT}testbench.vhd"
SIMULATION_CMD="${INSTALL_DIR}vsim -c scxml_lib.testbench -do automation.tcl"

# get arguments
TEST_NUMBER="test144.scxml"
if [ "$1" != "" ] ; then
  TEST_NUMBER="$1"
fi

# Write file
${SCXML_BIN}uscxml-transform -t vhdl -i ${SCXML_TEST}/w3c/ecma/${TEST_NUMBER} -o ${VHDL_OUT}dut.vhd
echo "$(cat ${VHDL_OUT}dut.vhd)"
echo "${VHDL_OUT}dut.vhd written"
TMP_RESULT="$(tail -n 1 ${VHDL_OUT}dut.vhd)"

if [ "$TMP_RESULT" == "ERROR" ] ; then
  echo "Error while generating VHDL"
  exit -1
fi


# compile stuff
cd ${SIM_DIR}
${COMPILE_CMD}
#/home/juehv/altera/13.1/modelsim_ase/bin/vcom  ${VHDL_OUT}dut.vhd testbench.vhd

if [ $? -eq 0 ] ; then
    echo "compilation done."
else
    echo "compilation failed"
    exit -1
fi

${SIMULATION_CMD}
