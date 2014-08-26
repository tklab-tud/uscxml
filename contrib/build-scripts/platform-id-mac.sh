#!/bin/bash

function version { 
	echo "$@" | awk -F. '{ printf("%03d%03d%03d\n", $1,$2,$3); }'; 
}

CMAKE_INFO=`cmake --system-information 2> /dev/null`

CURRENT_OSX_VERSION=`echo "$CMAKE_INFO" |grep CURRENT_OSX_VERSION |grep -v _CURRENT_OSX_VERSION | awk '{print $2}' |sed 's/\"//g'`
CMAKE_CXX_COMPILER_ID=`echo "$CMAKE_INFO" |grep 'CMAKE_CXX_COMPILER_ID ' | awk '{print tolower($2)}' |sed 's/\"//g' | sed 's/apple//g'`
CPU=`uname -m`

CPP_LIB="libc++"
if [ "$(version "10.9.0")" -gt "$(version "$CURRENT_OSX_VERSION")" ]; then
	# pre-mavericks
	CPP_LIB="libstdc++"
fi

echo "darwin-${CPU}-${CMAKE_CXX_COMPILER_ID}-${CPP_LIB}"
