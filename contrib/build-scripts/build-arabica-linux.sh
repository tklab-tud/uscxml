#!/bin/bash

#
# build arabica for Linux
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
CPUARCH=`uname -m`
PLATFORM_ID=`${DIR}/platform-id-linux.sh`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"

if [ ! -f src/arabica.cpp ]; then
	echo
	echo "Cannot find src/arabica.cpp"
	echo "Run script from within arabica directory:"
	echo "arabica $ ../../${ME}"
	echo
	exit
fi

if [ -f Makefile ]; then
  make clean
fi

./configure \
CFLAGS="-g" \
CXXFLAGS="-g" \
LDFLAGS="-g" \
--with-parser=libxml2 \
--with-tests=no \
--disable-shared \
--disable-dependency-tracking \
--with-pic \
--prefix=${DEST_DIR}

make
cp ./src/.libs/libarabica.a ./libarabica_d.a
make install # once for headers
rm ${DEST_DIR}/lib/libarabica*
make clean

./configure \
--with-parser=libxml2 \
--with-tests=no \
--disable-shared \
--disable-dependency-tracking \
--with-pic

make
cp ./src/.libs/libarabica.a ./libarabica.a
make clean

cp ./libarabica.a ${DEST_DIR}/lib
cp ./libarabica_d.a ${DEST_DIR}/lib