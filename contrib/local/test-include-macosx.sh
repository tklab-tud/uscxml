#!/bin/bash

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"

cd $DIR

HEADERS=`find ../../src -name *.h`

for HEADER in ${HEADERS}; do
  if [[ "$HEADER" == *inttypes.h* ]]; then 
		continue 
	fi
  if [[ "$HEADER" == *bindings* ]]; then 
		continue 
	fi
  if [[ "$HEADER" == *plugins* ]]; then 
		continue 
	fi
	echo ${HEADER}
	
	echo "\
#include \"${HEADER}\"
int main() {} " > test.cpp

	g++ \
		-I ${DIR}/../prebuilt/include \
		-I ${DIR}/../prebuilt/darwin-i386/10.9/clang/include/arabica \
		-I ${DIR}/../prebuilt/darwin-i386/10.9/clang/include \
		-I ${DIR}/../src/evws \
		-I /opt/local/include/libxml2 \
		-I /opt/local/lib/swipl-7.1.4/include \
		-I ${DIR}/../../src test.cpp
done