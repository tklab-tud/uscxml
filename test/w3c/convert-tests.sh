ME=`basename $0`
DIR="$( cd "$( dirname "$0" )" && pwd )"
cd $DIR

TXMLS=`ls txml/*.txml`

# see http://saxon.sourceforge.net/saxon6.5.1/using-xsl.html
for TXML in $TXMLS
do
	DEST=ecma/`basename $TXML .txml`.scxml
	echo "Processing $TXML to $DEST"
	java -jar /Users/sradomski/Developer/Applications/SaxonHE9-4-0-7J/saxon9he.jar $TXML confEcma.xsl -o:$DEST
done

for TXML in $TXMLS
do
	DEST=xpath/`basename $TXML .txml`.scxml
	echo "Processing $TXML to $DEST"
	java -jar /Users/sradomski/Developer/Applications/SaxonHE9-4-0-7J/saxon9he.jar $TXML confXPath.xsl -o:$DEST
done

cp txml/*.txt ecma/
cp txml/*.txt xpath/

find ./ecma -type f -exec grep -Ili 'datamodel="xpath"' {} \; |xargs rm -fv
find ./xpath -type f -exec grep -Ili 'datamodel="ecmascript"' {} \; |xargs rm -fv

SCXMLS=`find . -type f -name '*.scxml'`
for SCXML in $SCXMLS
do
	mv $SCXML $SCXML.unformatted.xml
	xmllint --format $SCXML.unformatted.xml > $SCXML
	rm $SCXML.unformatted.xml
done
