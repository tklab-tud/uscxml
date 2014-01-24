#!/bin/bash

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

cd $DIR

if [ "$USCXML_PREBUILT_HOST" == "" ]; then
	USCXML_PREBUILT_HOST="admin@uscxml.tk.informatik.tu-darmstadt.de"
fi

USCXML_PREBUILT_PATH="/var/www/html/uscxml/prebuilt"

if [ "$1" == "" ] || [ "$2" == "" ]; then
	echo "$ME <prebuilt dir> <version>"
	exit
fi

if [ ! -d $1 ]; then
	echo "$1: no such directory"
	exit
fi

VERSION=$2

cd ../prebuilt

ssh ${USCXML_PREBUILT_HOST} mkdir -p ${USCXML_PREBUILT_PATH}/${VERSION}

PLATFORMS=`find . -maxdepth 1 -type d -regex ./[^\.].*`
#PLATFORMS="linux-x86_64"
PLATFORMS="darwin-i386"
for FILE in ${PLATFORMS}; do
  PLATFORM=`basename $FILE`
  echo $FILE
  if [ "$PLATFORM" != "include" ]; then
    if [ "$PLATFORM" == windows* ]; then
      tar cvzf uscxml-prebuilt-${PLATFORM}.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' ${FILE}
    else
      tar cvzf uscxml-prebuilt-${PLATFORM}.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' --exclude='lib/*_d.a' ${FILE}
    fi
    scp uscxml-prebuilt-${PLATFORM}.tgz ${USCXML_PREBUILT_HOST}:${USCXML_PREBUILT_PATH}/${VERSION}
    rm uscxml-prebuilt-${PLATFORM}.tgz
  else
    tar cvzf include.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' ${FILE}
    scp include.tgz ${USCXML_PREBUILT_HOST}:${USCXML_PREBUILT_PATH}/${VERSION}
    rm include.tgz
  fi
done