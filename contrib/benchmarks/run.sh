#!/bin/bash
ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
CWD=`pwd`
cd ${DIR}

TIMEOUT=25s

RUN_QT=false
RUN_APACHE=false
RUN_SCION=false
RUN_SCXMLCC=false
RUN_USCXML=false
RUN_LXSC=false

PLOT=false

PATTERN='*.scxml'

if [ ! -d "./logs" ]; then
	mkdir logs
fi

# https://superuser.com/a/473715
function canonicalPath
{
    local path="$1" ; shift
    if [ -d "$path" ]
    then
        echo "$(cd "$path" ; pwd)"
    else
        local b=$(basename "$path")
        local p=$(dirname "$path")
        echo "$(cd "$p" ; pwd)/$b"
    fi
}

# ===== qt ================
function init-qt {
	cd qt
	if [ ! -x "./build/StatesPerSecond" ]; then
		mkdir build
		cd build
		qmake ..
		make
		cd ..
	fi
	cd ..
}

function run-qt {
	BENCHMARK=$1 
	SC_NAME=$2
	export USCXML_BENCHMARK=${BENCHMARK}

	cd qt/build
	make
	timeout ${TIMEOUT} ./StatesPerSecond |tee ../../logs/${SC_NAME}-qt.log
	cd ../..
}

function clean-qt {
	cd qt
	rm -rf build
	cd ..
}

# ===== APACHE ================
function init-apache {
	cd apache
	mvn compile
	cd ..
}

function run-apache {
	BENCHMARK=$1 
	SC_NAME=$2
	export USCXML_BENCHMARK=${BENCHMARK}

	cd apache
	timeout ${TIMEOUT} mvn test |tee ../logs/${SC_NAME}-apache.log
	cd ..

}

function clean-apache {
	cd apache
	rm -rf target
	cd ..
}


# ===== USCXML ================
function init-uscxml {
	cd uscxml
	if [ ! -x "./statesPerSecond" ]; then
		g++ -std=c++11 \
		./statesPerSecond.cpp \
		-I/usr/local/include \
		-I../../../build/cli/deps/xerces-c/include/ \
		-luscxml \
		-L ../../../build/cli/deps/xerces-c/lib/ \
		-lxerces-c \
		-o statesPerSecond
	fi
	cd ..
}

function run-uscxml {
	BENCHMARK=$1 
	SC_NAME=$2

	cd uscxml
	timeout 600s ./statesPerSecond ${BENCHMARK} fast
	timeout ${TIMEOUT} ./statesPerSecond ${BENCHMARK} fast |tee ../logs/${SC_NAME}-uscxml-fast.log
	USCXML_NOCACHE_FILES=YES \
	timeout ${TIMEOUT} ./statesPerSecond ${BENCHMARK} large |tee ../logs/${SC_NAME}-uscxml-large.log
	cd ..
}

function clean-uscxml {
	cd uscxml
	rm statesPerSecond
	cd ..

}

# ===== LXSC ================
function init-lxsc {
	cd lxsc

	if [ ! -d "./lxsc" ]; then
		git clone https://github.com/Phrogz/LXSC.git
		# increase microstep sequence considerably
		sed -i '.bak' 's/S\.MAX_ITERATIONS\ =\ 1000/S\.MAX_ITERATIONS\ =\ 1000000/' ./LXSC/lib/runtime.lua
	fi

	cd ..
}

function run-lxsc {
	BENCHMARK=$1 
	SC_NAME=$2

	cd lxsc
	timeout ${TIMEOUT} lua ./statesPerSecond.lua ${BENCHMARK} |tee ../logs/${SC_NAME}-lxsc.log
	cd ..
}

function clean-lxsc {
	cd lxsc
	rm -rf LXSC
	cd ..
}

# ===== SCION ================
function init-scion {
	cd scion
	if [ ! -d "./node_modules" ]; then
		npm install scxml babel-polyfill
	fi
	cd ..
}

function run-scion {
	BENCHMARK=$1 
	SC_NAME=$2

	cd scion

	timeout ${TIMEOUT} node ./statesPerSecond.js ${BENCHMARK} |tee ../logs/${SC_NAME}-scion.log

	cd ..
}

function clean-scion {
	cd scion
	rm -rf node_modules
	cd ..
}

# ===== SCXMLCC ================
function init-scxmlcc {
	cd scxmlcc

	# check out from git
	if [ ! -d "./scxmlcc" ]; then
		git clone https://github.com/jp-embedded/scxmlcc.git
	fi

	# compile transpiler
	if [ ! -x "./scxmlcc/src/scxmlcc" ]; then
		export CXXFLAGS=-I/opt/local/include
		cp ./makefile scxmlcc/src
		cd scxmlcc/src
		touch version_auto.h 
		make
		cd ../..
	fi

	cd ..
}

function run-scxmlcc {
	BENCHMARK=$1 
	SC_NAME=$2

	cd scxmlcc
	rm test
	timeout 600s ./scxmlcc/src/scxmlcc -i ${BENCHMARK} -o ./test.h
	timeout ${TIMEOUT} g++ -DMACHINE_NAME=sc_benchmark ./statesPerSecond.cpp -o test
	timeout ${TIMEOUT} ./test |tee ../logs/${SC_NAME}-scxmlcc.log

	cd ..
}

function clean-scxmlcc {
	cd scxmlcc
	rm -rf logs
	rm -rf scxmlcc
	rm test
	rm test.h
	cd ..
}  


# =======================================
while [[ $# -gt 0 ]]
do
key="$1"
case $key in
		-p|--pattern)
		PATTERN="$2"
		;;

		-p|--plot)
		
		;;
		-c|--clean)
		clean-scxmlcc
		clean-scion
		clean-lxsc
		clean-uscxml
		clean-apache
		clean-qt
		rm -rf logs
		exit
		;;

		--all)
		init-scxmlcc
		init-uscxml
		init-lxsc
		init-scion
		init-apache
		init-qt
		RUN_QT=true
		RUN_APACHE=true
		RUN_SCXMLCC=true
		RUN_USCXML=true
		RUN_LXSC=true
		RUN_SCION=true
		;;

		--scxmlcc)
		init-scxmlcc
		RUN_SCXMLCC=true
		;;

		--uscxml)
		init-uscxml
		RUN_USCXML=true
		;;

		--lxsc)
		init-lxsc
		RUN_LXSC=true
		;;

		--qt)
		init-qt
		RUN_QT=true
		;;

		--scion)
		init-scion
		RUN_SCION=true
		;;

		--apache)
		init-apache
		RUN_APACHE=true
		;;

		*)
		;;
esac
shift # past argument or value
done

BENCHMARKS=`find $(pwd)/../../test/benchmarks -type f -name ${PATTERN}`

for BENCHMARK in $BENCHMARKS
do
	BENCHMARK=$(canonicalPath $BENCHMARK)

	SC_NAME=$(basename "$BENCHMARK" .scxml)

	echo "== Running ${SC_NAME} from ${BENCHMARK}"
	
	if [ "$RUN_SCION" = true ] ; then
		echo "==== with SCION"
		run-scion ${BENCHMARK} ${SC_NAME}
	fi 

	if [ "$RUN_SCXMLCC" = true ] ; then
		echo "==== with SCXMLCC"
		run-scxmlcc ${BENCHMARK} ${SC_NAME}
	fi 

	if [ "$RUN_LXSC" = true ] ; then
		echo "==== with LXSC"
		run-lxsc ${BENCHMARK} ${SC_NAME}
	fi 

	if [ "$RUN_QT" = true ] ; then
		echo "==== with QT"
		run-qt ${BENCHMARK} ${SC_NAME}
	fi 

	if [ "$RUN_USCXML" = true ] ; then
		echo "==== with USCXML"
		run-uscxml ${BENCHMARK} ${SC_NAME}
	fi 

	if [ "$RUN_APACHE" = true ] ; then
		echo "==== with APACHE"
		run-apache ${BENCHMARK} ${SC_NAME}
	fi 

done
sed -i '.bak' '/^[0-9\.]*, [0-9\.]*/!d' ./logs/*.log
rm -f logs/*.bak

if [ "$PLOT" = true ] ; then
	./plot.sh
fi
