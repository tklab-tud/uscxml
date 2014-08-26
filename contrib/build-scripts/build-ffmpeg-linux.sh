#!/bin/bash

#
# build ffmpeg for Linux (Debian and Ubuntu)
#

# exit on error
set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )" 
CPUARCH=`uname -m`
PLATFORM_ID=`${DIR}/platform-id-linux.sh`
DEST_DIR="${DIR}/../prebuilt/${PLATFORM_ID}"

if [ -d /tmp/build-ffmpeg ]; then
  rm -rf /tmp/build-ffmpeg
fi
mkdir -p /tmp/build-ffmpeg
cd /tmp/build-ffmpeg

wget http://www.tortall.net/projects/yasm/releases/yasm-1.2.0.tar.gz
tar xzvf yasm-1.2.0.tar.gz
cd yasm-1.2.0
./configure --prefix="${DEST_DIR}" --bindir="${DEST_DIR}/bin"
make
make install
cd ..

export PATH=${PATH}:${DEST_DIR}/bin

git clone --depth 1 git://git.videolan.org/x264.git
cd x264
./configure --prefix="${DEST_DIR}" --bindir="${DEST_DIR}/bin" --enable-shared --enable-pic
make
make install
cd ..

git clone --depth 1 git://git.code.sf.net/p/opencore-amr/fdk-aac
cd fdk-aac
autoreconf -fiv
./configure --prefix="${DEST_DIR}" --enable-shared --with-pic
make
make install
cd ..

wget http://downloads.xiph.org/releases/opus/opus-1.0.3.tar.gz
tar xzvf opus-1.0.3.tar.gz
cd opus-1.0.3
./configure --prefix="${DEST_DIR}" --enable-shared --with-pic
make
make install
cd ..

git clone --depth 1 http://git.chromium.org/webm/libvpx.git
cd libvpx
./configure --prefix="${DEST_DIR}" --disable-examples --enable-shared --enable-pic
make
make install
cd ..

git clone --depth 1 git://source.ffmpeg.org/ffmpeg
cd ffmpeg
PKG_CONFIG_PATH="${DEST_DIR}/lib/pkgconfig"
export PKG_CONFIG_PATH
./configure --prefix="${DEST_DIR}" \
  --extra-cflags="-I${DEST_DIR}/include" --extra-ldflags="-L${DEST_DIR}/lib" \
  --bindir="${DEST_DIR}/bin" --extra-libs="-ldl" --enable-gpl --enable-nonfree \
  --enable-pic --disable-programs --disable-doc --enable-shared
make
make install
cd ..

