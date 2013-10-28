#!/bin/bash

#
# build libevent for MacOSX
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
MACOSX_VER=`/usr/bin/sw_vers -productVersion`
MACOSX_COMP=(`echo $MACOSX_VER | tr '.' ' '`)
DEST_DIR="${DIR}/../prebuilt/darwin-i386/${MACOSX_COMP[0]}.${MACOSX_COMP[1]}/gnu"

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

if [ ${MACOSX_COMP[1]} -lt 9 ]; then
  MACOSX_VERSION_MIN="-mmacosx-version-min=10.6"
fi

./configure \
CFLAGS="-g ${MACOSX_VERSION_MIN} -arch x86_64" \
CXXFLAGS="-g ${MACOSX_VERSION_MIN} -arch x86_64" \
LDFLAGS="-g ${MACOSX_VERSION_MIN} -arch x86_64" \
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
CFLAGS="${MACOSX_VERSION_MIN} -arch x86_64" \
CXXFLAGS="${MACOSX_VERSION_MIN} -arch x86_64" \
LDFLAGS="${MACOSX_VERSION_MIN} -arch x86_64" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ./libglog.x86_64.a
make clean


./configure \
CFLAGS="-g ${MACOSX_VERSION_MIN} -arch i386" \
CXXFLAGS="-g ${MACOSX_VERSION_MIN} -arch i386" \
LDFLAGS="-g ${MACOSX_VERSION_MIN} -arch i386" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ./libglog_d.i386.a
make clean


./configure \
CFLAGS="${MACOSX_VERSION_MIN} -arch i386" \
CXXFLAGS="${MACOSX_VERSION_MIN} -arch i386" \
LDFLAGS="${MACOSX_VERSION_MIN} -arch i386" \
--disable-rtti \
--enable-static \
--with-pic

make
cp ./.libs/libglog.a ./libglog.i386.a
make clean

lipo -create ./libglog.i386.a ./libglog.x86_64.a -output ${DEST_DIR}/lib/libglog.a
lipo -create ./libglog_d.i386.a ./libglog_d.x86_64.a -output ${DEST_DIR}/lib/libglog_d.a
