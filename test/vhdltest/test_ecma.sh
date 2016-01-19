#!/bin/bash

SCXML_TEST_DIR="/home/juehv/git/uscxml/test/w3c/ecma/"

TEST_SCRIPT_DIR="./"

for f in ${SCXML_TEST_DIR}*.scxml; do
  ${TEST_SCRIPT_DIR}write_dut.sh $f > tmp.log
  echo "$f $(tail -n 1 tmp.log)"
  echo "#####################" >> transscript.log
  echo "START $f" >> transscript.log
  echo "#####################" >> transscript.log
  echo "$(cat tmp.log)" >> transscript.log
  echo "#####################" >> transscript.log
  echo "END $f $(tail -n 1 tmp.log)" >> transscript.log
  echo "#####################" >> transscript.log
  echo " " >> transscript.log
done

