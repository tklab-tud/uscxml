#!/bin/bash

#
# build libevent for MacOSX
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
DEST_DIR="${DIR}/../prebuilt/darwin-i386/gnu"

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
CFLAGS="-g -mmacosx-version-min=10.6 -arch x86_64" \
CXXFLAGS="-g -mmacosx-version-min=10.6 -arch x86_64" \
LDFLAGS="-g -mmacosx-version-min=10.6 -arch x86_64" \
--disable-rtti \
--enable-static \
--with-pic \
--prefix=${DEST_DIR}

make
cp ./.libs/libglog.a ./libglog_d.x86_64.a
make install # once for headers
rm ${DEST_DIR}/lib/libglog*
make clean


./configure \
CFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
CXXFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
LDFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ./libglog.x86_64.a
make clean


./configure \
CFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
CXXFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
LDFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ./libglog_d.i386.a
make clean


./configure \
CFLAGS="-mmacosx-version-min=10.6 -arch i386" \
CXXFLAGS="-mmacosx-version-min=10.6 -arch i386" \
LDFLAGS="-mmacosx-version-min=10.6 -arch i386" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ./libglog.i386.a
make clean

lipo -create ./libglog.i386.a ./libglog.x86_64.a -output ${DEST_DIR}/lib/libglog.a
lipo -create ./libglog_d.i386.a ./libglog_d.x86_64.a -output ${DEST_DIR}/lib/libglog_d.a
