#!/bin/bash

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
IWYU="/usr/bin/iwyu"
CLANG="/usr/bin/clang++"

cd $DIR

mkdir uscxml
touch uscxml/config.h

#set -e

SOURCES=`find ../../src -name "*.cpp"`

for SOURCE in ${SOURCES}; do
  if [[ "$SOURCE" == *plugins* ]]; then 
		continue 
	fi
	echo ${SOURCE}
	
	${IWYU} -c \
		-I /usr/include \
		-I ${DIR}/../prebuilt/include \
		-I ${DIR}/../prebuilt/linux-i686/gnu/include/arabica \
		-I ${DIR}/../prebuilt/linux-i686/gnu/include \
		-I ${DIR}/../src/evws \
		-I /usr/include/libxml2 \
		-I ${DIR} \
		-I ${DIR}/../../src ${SOURCE}
done