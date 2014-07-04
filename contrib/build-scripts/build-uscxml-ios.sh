#!/bin/bash

#
# build all of uscxml for iOS and iOS simulator
#

# make sure this is not set
unset MACOSX_DEPLOYMENT_TARGET

# be ridiculously conservative with regard to ios features

if [ -z "${IPHONEOS_DEPLOYMENT_TARGET+xxx}" ]; then
	export IPHONEOS_DEPLOYMENT_TARGET="1.0"
fi

if [ -z "${IOS_SDK_VERSION+xxx}" ]; then
	export IOS_SDK_VERSION=7.1
fi

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`
BUILD_DIR="/tmp/build-uscxml-ios"

#rm -rf ${BUILD_DIR} && mkdir -p ${BUILD_DIR} &> /dev/null

#
# Build device with older SDK for old architectures
#
# export IOS_SDK_VERSION=5.1
#
# mkdir -p ${BUILD_DIR}/device-${IOS_SDK_VERSION}-debug &> /dev/null
# cd ${BUILD_DIR}/device-${IOS_SDK_VERSION}-debug
# cmake ${DIR}/../../ -DCMAKE_TOOLCHAIN_FILE=${DIR}/../cmake/CrossCompile-iOS.cmake -DDIST_PREPARE=ON -DCMAKE_BUILD_TYPE=Debug
# make -j4
#
# mkdir -p ${BUILD_DIR}/device-${IOS_SDK_VERSION}-release &> /dev/null
# cd ${BUILD_DIR}/device-${IOS_SDK_VERSION}-release
# cmake ${DIR}/../../ -DCMAKE_TOOLCHAIN_FILE=${DIR}/../cmake/CrossCompile-iOS.cmake -DDIST_PREPARE=ON -DCMAKE_BUILD_TYPE=Release
# make -j4

#
# Build device and sim with current SDK
#

mkdir -p ${BUILD_DIR}/device-${IOS_SDK_VERSION}-debug &> /dev/null
cd ${BUILD_DIR}/device-${IOS_SDK_VERSION}-debug
cmake ${DIR}/../../ -DCMAKE_TOOLCHAIN_FILE=${DIR}/../cmake/CrossCompile-iOS.cmake -DDIST_PREPARE=ON -DCMAKE_BUILD_TYPE=Debug
make -j4

mkdir -p ${BUILD_DIR}/simulator-${IOS_SDK_VERSION}-debug &> /dev/null
cd ${BUILD_DIR}/simulator-${IOS_SDK_VERSION}-debug
cmake ${DIR}/../../ -DCMAKE_TOOLCHAIN_FILE=${DIR}/../cmake/CrossCompile-iOS-Sim.cmake -DDIST_PREPARE=ON -DCMAKE_BUILD_TYPE=Debug
make -j4

mkdir -p ${BUILD_DIR}/device-${IOS_SDK_VERSION}-release &> /dev/null
cd ${BUILD_DIR}/device-${IOS_SDK_VERSION}-release
cmake ${DIR}/../../ -DCMAKE_TOOLCHAIN_FILE=${DIR}/../cmake/CrossCompile-iOS.cmake -DDIST_PREPARE=ON -DCMAKE_BUILD_TYPE=Release
make -j4

mkdir -p ${BUILD_DIR}/simulator-${IOS_SDK_VERSION}-release &> /dev/null
cd ${BUILD_DIR}/simulator-${IOS_SDK_VERSION}-release
cmake ${DIR}/../../ -DCMAKE_TOOLCHAIN_FILE=${DIR}/../cmake/CrossCompile-iOS-Sim.cmake -DDIST_PREPARE=ON -DCMAKE_BUILD_TYPE=Release
make -j4

#
# Create universal binary
#

LIBS=`find ${DIR}/../../package/cross-compiled/ios-* -name *.a`
set +e
for LIB in ${LIBS}; do
  LIB_BASE=`basename $LIB .a`
  ARCHS=`lipo -info $LIB`
  ARCHS=`expr "$ARCHS" : '.*:\(.*\)$'`
  for ARCH in ${ARCHS}; do
    mkdir -p ${DIR}/../../package/cross-compiled/ios/arch/${ARCH} > /dev/null
    lipo -extract $ARCH $LIB -output ${DIR}/../../package/cross-compiled/ios/arch/${ARCH}/${LIB_BASE}.a \
      || cp $LIB ${DIR}/../../package/cross-compiled/ios/arch/${ARCH}/${LIB_BASE}.a
    UNIQUE_LIBS=`ls ${DIR}/../../package/cross-compiled/ios/arch/${ARCH}`
  done
done

mkdir -p ${DIR}/../../package/cross-compiled/ios/lib &> /dev/null

for LIB in ${UNIQUE_LIBS}; do
  FILELIST=""
  for ARCH in `ls ${DIR}/../../package/cross-compiled/ios/arch/`; do
    FILELIST="${FILELIST} ${DIR}/../../package/cross-compiled/ios/arch/${ARCH}/${LIB}"
  done
  lipo -create ${FILELIST} -output ${DIR}/../../package/cross-compiled/ios/lib/${LIB}
done

# rm -rf ${DIR}/../../package/cross-compiled/ios/arch
# rm -rf ${DIR}/../../package/cross-compiled/ios-*/
