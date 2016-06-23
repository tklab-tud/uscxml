#!/bin/bash

#
# Convert all SCXML IRP tests from the W3C for specific datamodels
#

ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
cd $DIR

while [ "$1" != "" ]; do
	case $1 in
		ecma )
			ECMA=$1 
			shift ;;
		c89 )
			C89=$1 
			shift ;;
		lua )
			LUA=$1 
			shift ;;
		jexl ) 
			JEXL=$1 
			shift ;;
		namespace ) 
			NAMESPACE=$1 
			shift ;;
		xpath ) 
			XPATH=$1 
			shift ;;
		promela ) 
			PROMELA=$1 
			shift ;;
		prolog ) 
			PROLOG=$1 
			shift ;;
		* )
			echo "unknown datamodel $1"
			exit 1
	esac
done

TXMLS=`ls txml/*.txml`
TRANSFORM="java -jar /Users/sradomski/Developer/Applications/SaxonHE9-4-0-7J/saxon9he.jar"

# see http://saxon.sourceforge.net/saxon6.5.1/using-xsl.html
for TXML in $TXMLS
do
	echo -n "Processing $TXML for "
	TARGETFILE=`basename $TXML .txml`.scxml
	if [ "$ECMA" != "" ]; then
		echo -n "ecma " && $TRANSFORM $TXML confEcma.xsl -o:ecma/$TARGETFILE
	fi
	if [ "$C89" != "" ]; then
		echo -n "c89 " && $TRANSFORM $TXML confC89.xsl -o:c89/$TARGETFILE
	fi
	if [ "$JEXL" != "" ]; then
		echo -n "jexl " && $TRANSFORM $TXML confJEXL.xsl -o:jexl/$TARGETFILE
	fi
	if [ "$NAMESPACE" != "" ]; then
		echo -n "namespace " && $TRANSFORM ecma/$TARGETFILE confNamespace.xsl -o:namespace/$TARGETFILE
	fi
	if [ "$XPATH" != "" ]; then
		echo -n "xpath " && $TRANSFORM $TXML confXPath.xsl -o:xpath/$TARGETFILE
	fi
	if [ "$PROMELA" != "" ]; then
		echo -n "promela " && $TRANSFORM $TXML confPromela.xsl -o:promela/$TARGETFILE
	fi
	if [ "$PROLOG" != "" ]; then
		echo -n "prolog " && $TRANSFORM $TXML confProlog.xsl -o:prolog/$TARGETFILE
	fi
	if [ "$LUA" != "" ]; then
		echo -n "lua " && $TRANSFORM $TXML confLua.xsl -o:lua/$TARGETFILE
	fi
	echo
done

# make sure substitutions are idempotent!

if [ "$LUA" != "" ]; then
	# percent needs to be escaped in lua patterns
	sed -i.orig 's/this%20is%20some%20content/this%%20is%%20some%%20content/g' ./lua/test520.scxml

	# x-www-form-urlencode will not preserve the type and we default to string
	sed -i.orig 's/Var1==2/tonumber(Var1)==2/g' ./lua/test567.scxml
fi

if [ "$NAMESPACE" != "" ]; then
	# unnamespace embedded xml in namespace tests
	sed -i.orig 's/scxml:book/book/g' ./namespace/test557.scxml
	sed -i.orig 's/scxml:book/book/g' ./namespace/test561.scxml
fi

cp txml/*.txt ecma/
cp txml/*.txt namespace/
cp txml/*.txt xpath/
cp txml/*.txt promela/
cp txml/*.txt prolog/
cp txml/*.txt lua/
cp txml/*.txt jexl/

find ./ecma -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./namespace -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./xpath -type f -exec grep -Ili 'datamodel="ecmascript"' {} \; |xargs rm -fv

find ./promela -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./promela -type f -exec grep -Ili 'datamodel="ecmascript"' {} \; |xargs rm -fv
find ./promela -type f -exec grep -Ili 'datamodel="null"' {} \; |xargs rm -fv

find ./prolog -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./prolog -type f -exec grep -Ili 'datamodel="ecmascript"' {} \; |xargs rm -fv
find ./prolog -type f -exec grep -Ili 'datamodel="null"' {} \; |xargs rm -fv

find ./lua -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./lua -type f -exec grep -Ili 'datamodel="ecmascript"' {} \; |xargs rm -fv
find ./lua -type f -exec grep -Ili 'datamodel="null"' {} \; |xargs rm -fv

find ./jexl -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./jexl -type f -exec grep -Ili 'datamodel="ecmascript"' {} \; |xargs rm -fv
find ./jexl -type f -exec grep -Ili 'datamodel="null"' {} \; |xargs rm -fv

# test436 is the null datamodel
mv ./ecma/test436.scxml ./null
rm ./namespace/test436.scxml
rm ./xpath/test436.scxml
rm ./promela/test436.scxml
rm ./prolog/test436.scxml
rm ./lua/test436.scxml
rm ./jexl/test436.scxml

# format all SCXML files
SCXMLS=`find . -type f -name '*.scxml'`
for SCXML in $SCXMLS
do
	mv $SCXML $SCXML.unformatted.xml
	xmllint --format $SCXML.unformatted.xml > $SCXML
	rm $SCXML.unformatted.xml
done
