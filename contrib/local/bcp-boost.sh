#!/bin/sh

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

BOOST_DIR=$1
if [ ! -d ${BOOST_DIR} ]; then
	echo "First argument is supposed to be the path to the boost source code"
	exit
fi

cd $BOOST_DIR
./bootstrap.sh
./b2 tools/bcp

cd ${DIR}

SOURCE_FILES=`find ${DIR}/../../src/ -name \*.h -print -o -name \*.cpp -print`

${BOOST_DIR}/dist/bin/bcp \
--boost=${BOOST_DIR} \
--scan ${SOURCE_FILES} \
${DIR}/../src

# rm -rf ${DIR}/../prebuilt/include/libs
