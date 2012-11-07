#!/bin/bash

set -e

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`

find ${DIR}/../.. -name '.DS_Store' -exec rm {} \;