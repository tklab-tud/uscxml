#!/bin/bash

#
# build glog for iOS and iOS simulator
#

# make sure this is not set
unset MACOSX_DEPLOYMENT_TARGET

# be ridiculously conservative with regard to ios features
export IPHONEOS_DEPLOYMENT_TARGET="1.0"

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
#SDK_VER="6.1"
SDK_VER="5.1"
DEST_DIR="${DIR}/../prebuilt/ios/${SDK_VER}-glog-build"

if [ ! -f src/glog/logging.h ]; then
	echo
	echo "Cannot find src/glog/logging.h"
	echo "Run script from within glog directory:"
	echo "glog $ ../../${ME}"
	echo
	exit
fi

mkdir -p ${DEST_DIR} &> /dev/null

# see http://stackoverflow.com/questions/2424770/floating-point-comparison-in-shell-script
if [ $(bc <<< "$SDK_VER >= 6.1") -eq 1 ]; then
  DEV_ARCHS="-arch armv7 -arch armv7s"
elif [ $(bc <<< "$SDK_VER >= 5.1") -eq 1 ]; then
  DEV_ARCHS="-arch armv6 -arch armv7"
else
  echo
  echo "Building for SDK < 5.1 not supported"
  exit
fi

#
# Build for Device
#
if [ ! -d ${DEST_DIR}/device ]; then

  TOOLCHAIN_ROOT="/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneOS.platform/Developer" 
  SYSROOT="${TOOLCHAIN_ROOT}/SDKs/iPhoneOS${SDK_VER}.sdk"

  if [ ! -d ${SYSROOT} ]; then
    echo
    echo "Cannot find iOS developer tools at ${SYSROOT}."
    echo
    exit  
  fi

  if [ -f Makefile ]; then
    make clean
  fi

  mkdir -p ${DEST_DIR}/device &> /dev/null

  ./configure \
  CPP="cpp" \
  CXXCPP="cpp" \
  CXX=${TOOLCHAIN_ROOT}/usr/bin/g++ \
  CC=${TOOLCHAIN_ROOT}/usr/bin/gcc \
  LD=${TOOLCHAIN_ROOT}/usr/bin/ld\ -r \
  CFLAGS="-O -isysroot ${SYSROOT} ${DEV_ARCHS}" \
  CXXFLAGS="-O -isysroot ${SYSROOT} ${DEV_ARCHS}" \
  --host=arm-apple-darwin10 \
  --target=arm-apple-darwin10 \
  --disable-shared \
  --disable-dependency-tracking \
  LDFLAGS="-isysroot ${SYSROOT} ${DEV_ARCHS}" \
  AR=${TOOLCHAIN_ROOT}/usr/bin/ar \
  AS=${TOOLCHAIN_ROOT}/usr/bin/as \
  LIBTOOL=${TOOLCHAIN_ROOT}/usr/bin/libtool \
  STRIP=${TOOLCHAIN_ROOT}/usr/bin/strip \
  RANLIB=${TOOLCHAIN_ROOT}/usr/bin/ranlib \
  --prefix=${DEST_DIR}/device

  make -j2 install
else
  echo
  echo "${DEST_DIR}/device already exists - not rebuilding."
  echo
fi

#
# Simulator
#
if [ ! -d ${DEST_DIR}/simulator ]; then

  TOOLCHAIN_ROOT="/Applications/Xcode.app/Contents/Developer/Platforms/iPhoneSimulator.platform/Developer" 
  SYSROOT="${TOOLCHAIN_ROOT}/SDKs/iPhoneSimulator${SDK_VER}.sdk"

  if [ ! -d ${SYSROOT} ]; then
    echo
    echo "Cannot find iOS developer tools at ${SYSROOT}."
    echo
    exit  
  fi

  if [ -f Makefile ]; then
  	make clean
  fi

  mkdir -p ${DEST_DIR}/simulator &> /dev/null

  ./configure \
  CXX=${TOOLCHAIN_ROOT}/usr/bin/llvm-g++ \
  CC=${TOOLCHAIN_ROOT}/usr/bin/llvm-gcc \
  LD=${TOOLCHAIN_ROOT}/usr/bin/ld\ -r \
  CFLAGS="-O -isysroot ${SYSROOT} -arch i386" \
  CXXFLAGS="-O -isysroot ${SYSROOT} -arch i386" \
  --disable-shared \
  --disable-dependency-tracking \
  LDFLAGS="-isysroot  ${SYSROOT} -arch i386" \
  AR=${TOOLCHAIN_ROOT}/usr/bin/ar \
  AS=${TOOLCHAIN_ROOT}/usr/bin/as \
  LIBTOOL=${TOOLCHAIN_ROOT}/usr/bin/libtool \
  STRIP=${TOOLCHAIN_ROOT}/usr/bin/strip \
  RANLIB=${TOOLCHAIN_ROOT}/usr/bin/ranlib \
  --prefix=${DEST_DIR}/simulator

  make -j2 install
else
  echo
  echo "${DEST_DIR}/device already exists - not rebuilding."
  echo
fi

echo
echo "- Creating universal binaries --------------------------------------"
echo

LIBS=`find ${DIR}/../prebuilt/ios/*glog-build* -name *.a`
set +e
for LIB in ${LIBS}; do
  LIB_BASE=`basename $LIB .a`
  ARCHS=`lipo -info $LIB`
  ARCHS=`expr "$ARCHS" : '.*:\(.*\)$'`
  for ARCH in ${ARCHS}; do
    mkdir -p ${DIR}/../prebuilt/ios/arch/${ARCH} > /dev/null
    lipo -extract $ARCH $LIB -output ${DIR}/../prebuilt/ios/arch/${ARCH}/${LIB_BASE}.a \
      || cp $LIB ${DIR}/../prebuilt/ios/arch/${ARCH}/${LIB_BASE}.a
    UNIQUE_LIBS=`ls ${DIR}/../prebuilt/ios/arch/${ARCH}`
  done
done

mkdir -p ${DIR}/../prebuilt/ios/lib
for LIB in ${UNIQUE_LIBS}; do
  FILELIST=""
  for ARCH in `ls ${DIR}/../prebuilt/ios/arch/`; do
    FILELIST="${FILELIST} ${DIR}/../prebuilt/ios/arch/${ARCH}/${LIB}"
  done
  lipo -create ${FILELIST} -output ${DIR}/../prebuilt/ios/lib/${LIB}
done

rm -rf ${DIR}/../prebuilt/ios/arch/
