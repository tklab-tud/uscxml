#!/bin/sh

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

SOURCE_FILES=`find ${DIR}/../../src/ -name \*.h -print -o -name \*.cpp -print`

# echo ${ARABICA_FILES}
# exit

/Users/sradomski/Documents/TK/Code/boost_1_60_0/dist/bin/bcp \
--boost=/Users/sradomski/Documents/TK/Code/boost_1_60_0 \
--scan ${SOURCE_FILES} \
${DIR}/../src

# rm -rf ${DIR}/../prebuilt/include/libs
