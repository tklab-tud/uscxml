#!/bin/sh

set -e

git clone https://github.com/Phrogz/LXSC.git
cp ../../../test/benchmarks/findLCCA.scxml ./test.scxml

lua ./test-performance.lua