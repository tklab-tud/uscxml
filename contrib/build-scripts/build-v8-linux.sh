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
PWD=`pwd`

if [ ! -f src/v8.h ]; then
	echo
	echo "Cannot find src/v8.h"
	echo "Run script from within v8 directory"
	echo
	exit
fi

if [ ! -f ../depot_tools/update_depot_tools ]; then
	echo
	echo "Cannot find ../depot_tools/update_depot_tools"
	echo "Checkout depot_tools as a sibling directory"
	echo "svn co http://src.chromium.org/svn/trunk/tools/depot_tools"
	echo
	exit
fi

DEPOT_PATH="${PWD}/../depot_tools"
export PATH="${DEPOT_PATH}:${PATH}"

if [ "${CPUARCH}" = "x86_64" ]; then
  make x64.debug
  make x64.release
  
  cp ./out/x64.debug/obj.target/tools/gyp/libv8_base.x64.a ${DEST_DIR}/lib/libv8_base_d.a
  cp ./out/x64.debug/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot_d.a
  cp ./out/x64.release/obj.target/tools/gyp/libv8_base.x64.a ${DEST_DIR}/lib/libv8_base.a
  cp ./out/x64.release/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot.a
  
fi

if [ "${CPUARCH}" = "i686" ]; then
  make ia32.debug
  make ia32.release
  
  cp ./out/ia32.debug/obj.target/tools/gyp/libv8_base.ia32.a ${DEST_DIR}/lib/libv8_base_d.a
  cp ./out/ia32.debug/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot_d.a
  cp ./out/ia32.release/obj.target/tools/gyp/libv8_base.ia32.a ${DEST_DIR}/lib/libv8_base.a
  cp ./out/ia32.release/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot.a
  
fi

cp include/* ${DEST_DIR}/include
