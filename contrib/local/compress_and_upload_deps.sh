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
#PLATFORMS="linux-armv6l"
#PLATFORMS="darwin-i386"
#PLATFORMS="windows-x86"

for FILE in ${PLATFORMS}; do
	PLATFORM=`basename $FILE`
	echo $FILE
	case "$PLATFORM" in
	*linux-*-clang* | *darwin-*-gnu* )
	# do nothing - we will symlink
	;;
	"include")
		tar cvzf include.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' ${FILE}
		scp include.tgz ${USCXML_PREBUILT_HOST}:${USCXML_PREBUILT_PATH}/${VERSION}
		rm include.tgz
		;;
	*darwin*)
		cd $FILE
		# do not upload v8 for mac and strip first dir
		tar cvzf ../uscxml-prebuilt-${PLATFORM}.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' --exclude='lib/libv8*' --exclude='lib/*_d.a' *
		cd ..
		scp uscxml-prebuilt-${PLATFORM}.tgz ${USCXML_PREBUILT_HOST}:${USCXML_PREBUILT_PATH}/${VERSION}
		rm uscxml-prebuilt-${PLATFORM}.tgz
		;;
	*linux*)
		cd $FILE
		# no debug libs with linux and strip first dir
		tar cvzf ../uscxml-prebuilt-${PLATFORM}.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' --exclude='lib/*_d.a' *
		cd ..
		scp uscxml-prebuilt-${PLATFORM}.tgz ${USCXML_PREBUILT_HOST}:${USCXML_PREBUILT_PATH}/${VERSION}
		rm uscxml-prebuilt-${PLATFORM}.tgz
		;;
	*)
		cd $FILE
		# and strip first dir
		tar cvzf ../uscxml-prebuilt-${PLATFORM}.tgz --exclude='*/.DS_Store' --exclude='VERSION.txt' *
		cd ..
		scp uscxml-prebuilt-${PLATFORM}.tgz ${USCXML_PREBUILT_HOST}:${USCXML_PREBUILT_PATH}/${VERSION}
		rm uscxml-prebuilt-${PLATFORM}.tgz
		;;
	esac
done

# link ABI compatibles

for FILE in ${PLATFORMS}; do
	PLATFORM=`basename $FILE`

	case "$PLATFORM" in
		*linux-*-gnu* )
			# gcc is ABI compatible to clang
			NEW_PLATFORM="${PLATFORM//gnu/clang}"
			ssh ${USCXML_PREBUILT_HOST} \
				ln -s ${USCXML_PREBUILT_PATH}/${VERSION}/uscxml-prebuilt-${PLATFORM}.tgz \
							${USCXML_PREBUILT_PATH}/${VERSION}/uscxml-prebuilt-${NEW_PLATFORM}.tgz
		;;
		*darwin-*-clang* )
		# gcc is ABI compatible to clang
			NEW_PLATFORM="${PLATFORM//clang/gnu}"		
			ssh ${USCXML_PREBUILT_HOST} \
				ln -s ${USCXML_PREBUILT_PATH}/${VERSION}/uscxml-prebuilt-${PLATFORM}.tgz \
							${USCXML_PREBUILT_PATH}/${VERSION}/uscxml-prebuilt-${NEW_PLATFORM}.tgz
		;;
	esac
done