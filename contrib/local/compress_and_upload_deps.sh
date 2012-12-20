#!/bin/bash

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

cd $DIR

if [ "$UMUNDO_PREBUILT_HOST" == "" ]; then
	UMUNDO_PREBUILT_HOST="admin@uscxml.tk.informatik.tu-darmstadt.de:/var/www/html/uscxml/prebuilt"
fi

if [ "$1" == "" ] || [ "$2" == "" ]; then
	echo "$ME <prebuilt dir> <version>"
	exit
fi

if [ ! -d $1 ]; then
	echo "$1: no such directory"
	exit
fi

PLATFORM=`basename $1`
VERSION=$2

cd ../prebuilt

tar cvzf uscxml-prebuilt-${PLATFORM}.tgz ${PLATFORM}
scp uscxml-prebuilt-${PLATFORM}.tgz ${UMUNDO_PREBUILT_HOST}/${VERSION}
rm uscxml-prebuilt-${PLATFORM}.tgz