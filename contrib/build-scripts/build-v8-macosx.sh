#!/bin/bash

#
# build v8 for MacOSX
# http://code.google.com/p/v8/wiki/BuildingWithGYP
#

# exit on error
# set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
MACOSX_VER=`/usr/bin/sw_vers -productVersion`
MACOSX_COMP=(`echo $MACOSX_VER | tr '.' ' '`)
PLATFORM_ID=`${DIR}/platform-id-mac.sh`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"
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

if [ ${MACOSX_COMP[1]} -lt 9 ]; then
	export MACOSX_DEPLOYMENT_TARGET=10.6
	export GYP_DEFINES="clang=1 mac_deployment_target=10.6"
	export CXX="`which clang++` -mmacosx-version-min=10.6 -stdlib=libstdc++"
	export LINK="`which clang++` -stdlib=libstdc++"
  # export CXXFLAGS="-mmacosx-version-min=10.6 -stdlib=libstdc++"
  # export LDFLAGS="-stdlib=libstdc++"
else
	export MACOSX_DEPLOYMENT_TARGET=10.7
	export GYP_DEFINES="clang=1 mac_deployment_target=10.7"
	export CXX="`which clang++` -mmacosx-version-min=10.7 -stdlib=libc++"
	export LINK="`which clang++` -stdlib=libc++"
  # export CXXFLAGS="-mmacosx-version-min=10.7 -stdlib=libc++"
  # export LDFLAGS="-stdlib=libc++"
fi

# make dependencies

make snapshot=off ia32.release
make snapshot=off ia32.debug

make snapshot=off x64.release
make snapshot=off x64.debug

cp include/*.h ${DEST_DIR}/include

#release 
lipo -create \
  ./out/x64.release/libv8_base.a \
  ./out/ia32.release/libv8_base.a \
  -output ${DEST_DIR}/lib/libv8_base.a

lipo -create \
  ./out/x64.release/libv8_libbase.a \
  ./out/ia32.release/libv8_libbase.a \
  -output ${DEST_DIR}/lib/libv8_libbase.a

lipo -create \
  ./out/x64.release/libv8_libplatform.a \
  ./out/ia32.release/libv8_libplatform.a \
  -output ${DEST_DIR}/lib/libv8_libplatform.a

lipo -create \
  ./out/x64.release/libv8_external_snapshot.a \
  ./out/ia32.release/libv8_external_snapshot.a \
  -output ${DEST_DIR}/lib/libv8_external_snapshot.a

lipo -create \
  ./out/x64.release/libicuuc.a \
  ./out/ia32.release/libicuuc.a \
  -output ${DEST_DIR}/lib/libicuuc.a

lipo -create \
  ./out/x64.release/libicui18n.a \
  ./out/ia32.release/libicui18n.a \
  -output ${DEST_DIR}/lib/libicui18n.a

lipo -create \
  ./out/x64.release/libicudata.a \
  ./out/ia32.release/libicudata.a \
  -output ${DEST_DIR}/lib/libicudata.a

#debug
lipo -create \
  ./out/x64.debug/libv8_base.a \
  ./out/ia32.debug/libv8_base.a \
  -output ${DEST_DIR}/lib/libv8_base_d.a
  
lipo -create \
  ./out/x64.debug/libv8_libbase.a \
  ./out/ia32.debug/libv8_libbase.a \
  -output ${DEST_DIR}/lib/libv8_libbase_d.a

lipo -create \
  ./out/x64.debug/libv8_libplatform.a \
  ./out/ia32.debug/libv8_libplatform.a \
  -output ${DEST_DIR}/lib/libv8_libplatform_d.a

lipo -create \
  ./out/x64.debug/libv8_external_snapshot.a \
  ./out/ia32.debug/libv8_external_snapshot.a \
  -output ${DEST_DIR}/lib/libv8_external_snapshot_d.a


lipo -create \
  ./out/x64.debug/libicuuc.a \
  ./out/ia32.debug/libicuuc.a \
  -output ${DEST_DIR}/lib/libicuuc_d.a

lipo -create \
  ./out/x64.debug/libicui18n.a \
  ./out/ia32.debug/libicui18n.a \
  -output ${DEST_DIR}/lib/libicui18n_d.a

lipo -create \
  ./out/x64.debug/libicudata.a \
  ./out/ia32.debug/libicudata.a \
  -output ${DEST_DIR}/lib/libicudata_d.a
