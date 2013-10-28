#!/bin/bash

#
# build libevent for linux
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
CPUARCH=`uname -m`
DEST_DIR="${DIR}/../prebuilt/linux-${CPUARCH}/gnu"

if [ ! -f event.c ]; then
	echo
	echo "Cannot find event.c"
	echo "Run script from within libevent directory"
	echo
	exit
fi

rm lib*.a

if [ -f Makefile ]; then
  make clean
fi

./configure \
CFLAGS="-g" \
CXXFLAGS="-g" \
LDFLAGS="-g" \
--enable-gcc-hardening \
--with-pic \
--prefix=${DEST_DIR}

make
cp ./.libs/libevent.a ./libevent_d.a
cp ./.libs/libevent_core.a ./libevent_core_d.a
cp ./.libs/libevent_extra.a ./libevent_extra_d.a
cp ./.libs/libevent_openssl.a ./libevent_openssl_d.a
cp ./.libs/libevent_pthreads.a ./libevent_pthreads_d.a
make install # once for headers
rm ${DEST_DIR}/lib/libevent*
make clean


./configure \
--enable-gcc-hardening \
--with-pic \
--disable-debug-mode \
--disable-libevent-install

make
cp ./.libs/libevent.a ./libevent.a
cp ./.libs/libevent_core.a ./libevent_core.a
cp ./.libs/libevent_extra.a ./libevent_extra.a
cp ./.libs/libevent_openssl.a ./libevent_openssl.a
cp ./.libs/libevent_pthreads.a ./libevent_pthreads.a
make clean

cp ./*.a ${DEST_DIR}/lib
