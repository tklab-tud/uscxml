#!/bin/bash

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

if [ ! -f "docs/html/index.html" ]
then
	echo "No documentation found in docs/html - run from build dir after make docs"
	exit
fi

DOCS="${CWD}/docs/html"

tempfoo=`basename $0`
TMPDIR=`mktemp -d /tmp/${tempfoo}.XXXXXX` || exit 1
cd ${TMPDIR}

git clone -b gh-pages git@github.com:tklab-tud/uscxml.git
rm -rf uscxml/*
cp -R /Users/sradomski/Documents/TK/Code/uscxml/build/cli/docs/html/ ./uscxml/
cd uscxml
git add -A
git commit -m "Updated documentation"
git push
