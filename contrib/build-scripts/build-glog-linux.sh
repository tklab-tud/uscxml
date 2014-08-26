#!/bin/bash

#
# build libevent for linux
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
CPUARCH=`uname -m`
PLATFORM_ID=`${DIR}/platform-id-linux.sh`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"

if [ ! -f src/glog/log_severity.h ]; then
	echo
	echo "Cannot find src/glog/log_severity.h"
	echo "Run script from within glog directory"
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
--disable-rtti \
--enable-static \
--with-pic \
--prefix=${DEST_DIR}

make
make install # once for headers
rm ${DEST_DIR}/lib/libglog*
cp ./.libs/libglog.a ${DEST_DIR}/lib/libglog_d.a
make clean

./configure \
CFLAGS="-g" \
CXXFLAGS="-g" \
LDFLAGS="-g" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ${DEST_DIR}/lib/libglog.a
