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
PWD=`pwd`

if [ "${CPUARCH}" = "i686" ]; then
	echo
	echo "v8 will no longer compile on 32bit"
	echo "Start from a 64bit host and we will cross-compile"
	echo
	exit
fi

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

# export CXX="`which clang++` -fPIC"
export CFLAGS="-fPIC" 
export CXXFLAGS="-fPIC"
export GYPFLAGS="-Dv8_use_external_startup_data=0"

DEPOT_PATH="${PWD}/../depot_tools"
export PATH="${DEPOT_PATH}:${PATH}"

PLATFORM_ID=`${DIR}/platform-id-linux.sh x86_64`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"

cp include/*.h ${DEST_DIR}/include

make V=1 x64.debug
make V=1 x64.release

# libv8_external_snapshot.a
# libv8_libplatform.a
# libv8_base.a
# libv8_libbase.a
# libv8_nosnapshot.a


cp ./out/x64.debug/obj.target/tools/gyp/libv8_external_snapshot.a ${DEST_DIR}/lib/libv8_external_snapshot_d.a
cp ./out/x64.debug/obj.target/tools/gyp/libv8_libplatform.a ${DEST_DIR}/lib/libv8_libplatform_d.a
cp ./out/x64.debug/obj.target/tools/gyp/libv8_base.a ${DEST_DIR}/lib/libv8_base_d.a
cp ./out/x64.debug/obj.target/tools/gyp/libv8_libbase.a ${DEST_DIR}/lib/libv8_libbase_d.a
cp ./out/x64.debug/obj.target/tools/gyp/libv8_nosnapshot.a ${DEST_DIR}/lib/libv8_nosnapshot_d.a
cp ./out/x64.debug/obj.target/third_party/icu/libicuuc.a ${DEST_DIR}/lib/libicuuc_d.a
cp ./out/x64.debug/obj.target/third_party/icu/libicui18n.a ${DEST_DIR}/lib/libicui18n_d.a
cp ./out/x64.debug/obj.target/third_party/icu/libicudata.a ${DEST_DIR}/lib/libicudata_d.a


cp ./out/x64.release/obj.target/tools/gyp/libv8_external_snapshot.a ${DEST_DIR}/lib/libv8_external_snapshot.a
cp ./out/x64.release/obj.target/tools/gyp/libv8_libplatform.a ${DEST_DIR}/lib/libv8_libplatform.a
cp ./out/x64.release/obj.target/tools/gyp/libv8_base.a ${DEST_DIR}/lib/libv8_base.a
cp ./out/x64.release/obj.target/tools/gyp/libv8_libbase.a ${DEST_DIR}/lib/libv8_libbase.a
cp ./out/x64.release/obj.target/tools/gyp/libv8_nosnapshot.a ${DEST_DIR}/lib/libv8_nosnapshot.a
cp ./out/x64.release/obj.target/third_party/icu/libicuuc.a ${DEST_DIR}/lib/libicuuc.a
cp ./out/x64.release/obj.target/third_party/icu/libicui18n.a ${DEST_DIR}/lib/libicui18n.a
cp ./out/x64.release/obj.target/third_party/icu/libicudata.a ${DEST_DIR}/lib/libicudata.a


PLATFORM_ID=`${DIR}/platform-id-linux.sh i686`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"

cp include/*.h ${DEST_DIR}/include

make V=1 ia32.debug
make V=1 ia32.release

cp ./out/ia32.debug/obj.target/tools/gyp/libv8_external_snapshot.a ${DEST_DIR}/lib/libv8_external_snapshot_d.a
cp ./out/ia32.debug/obj.target/tools/gyp/libv8_libplatform.a ${DEST_DIR}/lib/libv8_libplatform_d.a
cp ./out/ia32.debug/obj.target/tools/gyp/libv8_base.a ${DEST_DIR}/lib/libv8_base_d.a
cp ./out/ia32.debug/obj.target/tools/gyp/libv8_libbase.a ${DEST_DIR}/lib/libv8_libbase_d.a
cp ./out/ia32.debug/obj.target/tools/gyp/libv8_nosnapshot.a ${DEST_DIR}/lib/libv8_nosnapshot_d.a
cp ./out/ia32.debug/obj.target/third_party/icu/libicuuc.a ${DEST_DIR}/lib/libicuuc_d.a
cp ./out/ia32.debug/obj.target/third_party/icu/libicui18n.a ${DEST_DIR}/lib/libicui18n_d.a
cp ./out/ia32.debug/obj.target/third_party/icu/libicudata.a ${DEST_DIR}/lib/libicudata_d.a

cp ./out/ia32.release/obj.target/tools/gyp/libv8_external_snapshot.a ${DEST_DIR}/lib/libv8_external_snapshot.a
cp ./out/ia32.release/obj.target/tools/gyp/libv8_libplatform.a ${DEST_DIR}/lib/libv8_libplatform.a
cp ./out/ia32.release/obj.target/tools/gyp/libv8_base.a ${DEST_DIR}/lib/libv8_base.a
cp ./out/ia32.release/obj.target/tools/gyp/libv8_libbase.a ${DEST_DIR}/lib/libv8_libbase.a
cp ./out/ia32.release/obj.target/tools/gyp/libv8_nosnapshot.a ${DEST_DIR}/lib/libv8_nosnapshot.a
cp ./out/ia32.release/obj.target/third_party/icu/libicuuc.a ${DEST_DIR}/lib/libicuuc.a
cp ./out/ia32.release/obj.target/third_party/icu/libicui18n.a ${DEST_DIR}/lib/libicui18n.a
cp ./out/ia32.release/obj.target/third_party/icu/libicudata.a ${DEST_DIR}/lib/libicudata.a

# if [ "${CPUARCH}" = "x86_64" ]; then
#   make x64.debug
#   make x64.release
#
#   # cp ./out/x64.debug/obj.target/tools/gyp/libv8_base.x64.a ${DEST_DIR}/lib/libv8_base_d.a
#   # cp ./out/x64.debug/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot_d.a
#   # cp ./out/x64.release/obj.target/tools/gyp/libv8_base.x64.a ${DEST_DIR}/lib/libv8_base.a
#   # cp ./out/x64.release/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot.a
#
# fi
#
# if [ "${CPUARCH}" = "i686" ]; then
#   make ia32.debug
#   make ia32.release
#
#   # cp ./out/ia32.debug/obj.target/tools/gyp/libv8_base.ia32.a ${DEST_DIR}/lib/libv8_base_d.a
#   # cp ./out/ia32.debug/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot_d.a
#   # cp ./out/ia32.release/obj.target/tools/gyp/libv8_base.ia32.a ${DEST_DIR}/lib/libv8_base.a
#   # cp ./out/ia32.release/obj.target/tools/gyp/libv8_snapshot.a ${DEST_DIR}/lib/libv8_snapshot.a
#
# fi
#
