#!/bin/bash

#
# build v8 for MacOSX
# http://code.google.com/p/v8/wiki/BuildingWithGYP
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
MACOSX_VER=`/usr/bin/sw_vers -productVersion`
MACOSX_COMP=(`echo $MACOSX_VER | tr '.' ' '`)
PLATFORM_ID=`${DIR}/platform-id-mac.sh`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"
PWD=`pwd`

export MACOSX_DEPLOYMENT_TARGET=10.6

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
  CXXFLAGS="-mmacosx-version-min=10.6 -stdlib=libstdc++"
  LDFLAGS="-stdlib=libstdc++"
else
  CXXFLAGS="-mmacosx-version-min=10.7 -stdlib=libc++"
  LDFLAGS="-stdlib=libc++"
fi

make dependencies

make ia32.release
make ia32.debug

make x64.release
make x64.debug

cp include/* ${DEST_DIR}/include

lipo -create \
  ./out/x64.release/libv8_base.x64.a \
  ./out/ia32.release/libv8_base.ia32.a \
  -output ${DEST_DIR}/lib/libv8_base.a
  
lipo -create \
  ./out/x64.release/libv8_snapshot.a \
  ./out/ia32.release/libv8_snapshot.a \
  -output ${DEST_DIR}/lib/libv8_snapshot.a
  
lipo -create \
  ./out/x64.debug/libv8_base.x64.a \
  ./out/ia32.debug/libv8_base.ia32.a \
  -output ${DEST_DIR}/lib/libv8_base_d.a
  
lipo -create \
  ./out/x64.debug/libv8_snapshot.a \
  ./out/ia32.debug/libv8_snapshot.a \
  -output ${DEST_DIR}/lib/libv8_snapshot_d.a
  

