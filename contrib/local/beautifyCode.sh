#!/bin/bash

# see http://astyle.sourceforge.net/astyle.html
# run from project root as sh ./contrib/tidy_source.sh

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

find ${DIR}/../../ -name ".DS_Store" -exec rm {} \;

astyle  \
	--style=java \
	--indent=tab \
	--recursive "${DIR}/../../src/*.cpp" "${DIR}/../../src/*.h"
find ${DIR}/../../src/ -iname '*.orig' -exec rm {} \;

astyle  \
	--style=java \
	--indent=tab \
	--recursive "${DIR}/../../test/*.cpp"
find ${DIR}/../../test/ -iname '*.orig' -exec rm {} \;
