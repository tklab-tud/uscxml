#!/bin/bash

#
# build libevent for MacOSX
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
DEST_DIR="${DIR}/../prebuilt/darwin-i386/gnu"

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
CFLAGS="-g -mmacosx-version-min=10.6 -arch x86_64" \
CXXFLAGS="-g -mmacosx-version-min=10.6 -arch x86_64" \
LDFLAGS="-g -mmacosx-version-min=10.6 -arch x86_64" \
--with-libxml2=${SYSROOT}/usr \
--with-parser=libxml2 \
--with-tests=no \
--with-boost=/opt/local/include \
--disable-shared \
--disable-dependency-tracking \
--with-pic \
--prefix=${DEST_DIR}


make
cp ./src/.libs/libarabica.a ./libarabica_d.x86_64.a
make install # once for headers
rm ${DEST_DIR}/lib/libarabica*
make clean


./configure \
CFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
CXXFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
LDFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
--with-libxml2=${SYSROOT}/usr \
--with-parser=libxml2 \
--with-tests=no \
--with-boost=/opt/local/include \
--disable-shared \
--disable-dependency-tracking \
--with-pic

make
cp ./src/.libs/libarabica.a ./libarabica.x86_64.a
make clean


./configure \
CFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
CXXFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
LDFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
--with-libxml2=${SYSROOT}/usr \
--with-parser=libxml2 \
--with-tests=no \
--with-boost=/opt/local/include \
--disable-shared \
--disable-dependency-tracking \
--with-pic

make
cp ./src/.libs/libarabica.a ./libarabica_d.i386.a
make clean

./configure \
CFLAGS="-mmacosx-version-min=10.6 -arch i386" \
CXXFLAGS="-mmacosx-version-min=10.6 -arch i386" \
LDFLAGS="-mmacosx-version-min=10.6 -arch i386" \
--with-libxml2=${SYSROOT}/usr \
--with-parser=libxml2 \
--with-tests=no \
--with-boost=/opt/local/include \
--disable-shared \
--disable-dependency-tracking \
--with-pic

make
cp ./src/.libs/libarabica.a ./libarabica.i386.a
make clean


lipo -create ./libarabica.i386.a ./libarabica.x86_64.a -output ${DEST_DIR}/lib/libarabica.a
lipo -create ./libarabica_d.i386.a ./libarabica_d.x86_64.a -output ${DEST_DIR}/lib/libarabica_d.a
