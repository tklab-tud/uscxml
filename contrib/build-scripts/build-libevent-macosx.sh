#!/bin/bash

#
# build libevent for MacOSX
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
DEST_DIR="${DIR}/../prebuilt/darwin-i386/gnu"

if [ ! -f event.c ]; then
	echo
	echo "Cannot find event.c"
	echo "Run script from within libevent directory"
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
--enable-gcc-hardening \
--with-pic \
--prefix=${DEST_DIR}

# not available on 10.6
sed -iold s/define\ HAVE_ARC4RANDOM_BUF\ 1/undef\ HAVE_ARC4RANDOM_BUF/ config.h

make
cp ./.libs/libevent.a ./libevent_d.x86_64.a
cp ./.libs/libevent_core.a ./libevent_core_d.x86_64.a
cp ./.libs/libevent_extra.a ./libevent_extra_d.x86_64.a
cp ./.libs/libevent_openssl.a ./libevent_openssl_d.x86_64.a
cp ./.libs/libevent_pthreads.a ./libevent_pthreads_d.x86_64.a
make install # once for headers
rm ${DEST_DIR}/lib/libevent*
make clean

./configure \
CFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
CXXFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
LDFLAGS="-mmacosx-version-min=10.6 -arch x86_64" \
--enable-gcc-hardening \
--with-pic \
--disable-debug-mode \
--disable-libevent-install

sed -iold s/define\ HAVE_ARC4RANDOM_BUF\ 1/undef\ HAVE_ARC4RANDOM_BUF/ config.h

make
cp ./.libs/libevent.a ./libevent.x86_64.a
cp ./.libs/libevent_core.a ./libevent_core.x86_64.a
cp ./.libs/libevent_extra.a ./libevent_extra.x86_64.a
cp ./.libs/libevent_openssl.a ./libevent_openssl.x86_64.a
cp ./.libs/libevent_pthreads.a ./libevent_pthreads.x86_64.a
make clean


./configure \
CFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
CXXFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
LDFLAGS="-g -mmacosx-version-min=10.6 -arch i386" \
--enable-gcc-hardening \
--with-pic \
--disable-libevent-install

sed -iold s/define\ HAVE_ARC4RANDOM_BUF\ 1/undef\ HAVE_ARC4RANDOM_BUF/ config.h

make
cp ./.libs/libevent.a ./libevent_d.i386.a
cp ./.libs/libevent_core.a ./libevent_core_d.i386.a
cp ./.libs/libevent_extra.a ./libevent_extra_d.i386.a
cp ./.libs/libevent_openssl.a ./libevent_openssl_d.i386.a
cp ./.libs/libevent_pthreads.a ./libevent_pthreads_d.i386.a
make clean

./configure \
CFLAGS="-mmacosx-version-min=10.6 -arch i386" \
CXXFLAGS="-mmacosx-version-min=10.6 -arch i386" \
LDFLAGS="-mmacosx-version-min=10.6 -arch i386" \
--enable-gcc-hardening \
--with-pic \
--disable-debug-mode \
--disable-libevent-install

sed -iold s/define\ HAVE_ARC4RANDOM_BUF\ 1/undef\ HAVE_ARC4RANDOM_BUF/ config.h

make
cp ./.libs/libevent.a ./libevent.i386.a
cp ./.libs/libevent_core.a ./libevent_core.i386.a
cp ./.libs/libevent_extra.a ./libevent_extra.i386.a
cp ./.libs/libevent_openssl.a ./libevent_openssl.i386.a
cp ./.libs/libevent_pthreads.a ./libevent_pthreads.i386.a
make clean

lipo -create ./libevent.i386.a ./libevent.x86_64.a -output ${DEST_DIR}/lib/libevent.a
lipo -create ./libevent_core.i386.a ./libevent_core.x86_64.a -output ${DEST_DIR}/lib/libevent_core.a
lipo -create ./libevent_extra.i386.a ./libevent_extra.x86_64.a -output ${DEST_DIR}/lib/libevent_extra.a
lipo -create ./libevent_openssl.i386.a ./libevent_openssl.x86_64.a -output ${DEST_DIR}/lib/libevent_openssl.a
lipo -create ./libevent_pthreads.i386.a ./libevent_pthreads.x86_64.a -output ${DEST_DIR}/lib/libevent_pthreads.a

lipo -create ./libevent_d.i386.a ./libevent_d.x86_64.a -output ${DEST_DIR}/lib/libevent_d.a
lipo -create ./libevent_core_d.i386.a ./libevent_core_d.x86_64.a -output ${DEST_DIR}/lib/libevent_core_d.a
lipo -create ./libevent_extra_d.i386.a ./libevent_extra_d.x86_64.a -output ${DEST_DIR}/lib/libevent_extra_d.a
lipo -create ./libevent_openssl_d.i386.a ./libevent_openssl_d.x86_64.a -output ${DEST_DIR}/lib/libevent_openssl_d.a
lipo -create ./libevent_pthreads_d.i386.a ./libevent_pthreads_d.x86_64.a -output ${DEST_DIR}/lib/libevent_pthreads_d.a
