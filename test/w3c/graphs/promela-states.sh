#!/bin/bash

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"

mkdir ${DIR}/data  &> /dev/null

${DIR}/../analyze_promela_tests.pl w3c pml.states.stateSize pml.memory.actual flat.actualComplexity > ${DIR}/data/pml_states.data

cat ${DIR}/data/pml_states.data | gnuplot -p -e 'plot "-" with lines,"-" with lines'