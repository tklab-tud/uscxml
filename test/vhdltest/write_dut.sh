#!/bin/bash
SCXML_BIN=/home/juehv/git/uscxml/build/bin/

SIM_DIR=/home/juehv/modelsim/automated_test/
INSTALL_DIR=/home/juehv/altera/13.1/modelsim_ase/bin/
VHDL_OUT=${SIM_DIR}vhd/

COMPILE_CMD="${INSTALL_DIR}vcom ${VHDL_OUT}dut.vhd "
SIMULATION_CMD="${INSTALL_DIR}vsim -c scxml_lib.dut -do automation.tcl"

# get arguments
SCXML_TEST="/home/juehv/git/uscxml/test/w3c/ecma/test144.scxml"
if [ "$1" != "" ] ; then
  SCXML_TEST="$1"
fi
echo "Use file ${SCXML_TEST}"

# Write VHDL file
${SCXML_BIN}uscxml-transform -t vhdl -i ${SCXML_TEST} -o ${VHDL_OUT}dut.vhd
#echo "$(cat ${VHDL_OUT}dut.vhd)"

echo "${VHDL_OUT}dut.vhd written"
TMP_RESULT="$(tail -n 1 ${VHDL_OUT}dut.vhd)"

if [ "$TMP_RESULT" == "ERROR" ] ; then
  echo "$(cat ${VHDL_OUT}dut.vhd)"
  echo "Error while generating VHDL"
  echo "FAILED"
  exit -1
fi


# compile stuff
cd ${SIM_DIR}
${COMPILE_CMD}

if [ $? -eq 0 ] ; then
    echo "compilation done."
else
    echo "compilation failed"
    echo "FAILED"
    exit -1
fi
exit 0
# simulate the hardware
# simulator will drop FAILED or PASSED
cd ${SIM_DIR}
#${SIMULATION_CMD}


TMP_RESULT="$(tail -n 1 ${SIM_DIR}transcript)"

if [ "$TMP_RESULT" != "OK" ] ; then
  echo "Error while simulating VHDL"
  echo "$TMP_RESULT"
  exit -1
else 
  echo "OK"
  exit 0
fi

