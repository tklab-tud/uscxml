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
