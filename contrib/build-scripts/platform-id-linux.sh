#!/bin/bash

function version { 
	echo "$@" | awk -F. '{ printf("%03d%03d%03d\n", $1,$2,$3); }'; 
}

CMAKE_INFO=`cmake --system-information 2> /dev/null`

CMAKE_CXX_COMPILER_ID=`echo "$CMAKE_INFO" |grep 'CMAKE_CXX_COMPILER_ID ' | awk '{print tolower($2)}' |sed 's/\"//g'`
CPU=`uname -m`

if (( $# > 0 )); then
	CPU=$1
fi

echo "linux-${CPU}-${CMAKE_CXX_COMPILER_ID}"
