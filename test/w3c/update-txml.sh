#!/bin/bash

#
# Download / update all SCXML IRP tests from the W3C
#

wget -rl1 -Atxml,txt,xsl http://www.w3.org/Voice/2013/scxml-irp/

# wget http://www.w3.org/Voice/2013/scxml-irp/545/test545.txml
# wget http://www.w3.org/Voice/2013/scxml-irp/577/test577.txml
# mv test545.txml ./txml
# mv test577.txml ./txml

find ./www.w3.org -name "*.txml" -exec cp {} ./txml \;
find ./www.w3.org -name "*.txt" -exec cp {} ./txml \;
find ./www.w3.org -name "*.xsl" -exec cp {} . \;
rm -rf www.w3.org

# sed -ie "s/<xsl:attribute name=\"delayexpr\">Var<xsl:value-of select=\".\" \/><\/xsl:attribute>/<xsl:attribute name=\"delayexpr\">(Var<xsl:value-of select=\".\" \/>.slice(0, - 1)) * 50 + 'ms'<\/xsl:attribute>/" confEcma.xsl
# sed -ie "s/<xsl:attribute name=\"delayexpr\">'<xsl:value-of select=\".\"\/>s'<\/xsl:attribute>/<xsl:attribute name=\"delayexpr\">'<xsl:value-of select=\". * 50\"\/>ms'<\/xsl:attribute>/" confEcma.xsls
#rm confEcma.xsle
