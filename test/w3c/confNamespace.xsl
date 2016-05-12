<xsl:stylesheet version="1.0"
 xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
 xmlns:scxml="http://www.w3.org/2005/07/scxml">
 <xsl:output omit-xml-declaration="no" indent="yes"/>

 <xsl:template match="node()|@*">
  <xsl:copy>
   <xsl:apply-templates select="node()|@*"/>
  </xsl:copy>
 </xsl:template>

 <xsl:template match="*">
  <xsl:element name="scxml:{name()}" namespace="http://www.w3.org/2005/07/scxml">
    <xsl:copy-of select="namespace::*"/>
    <xsl:apply-templates select="node()|@*"/>
  </xsl:element>
 </xsl:template>
</xsl:stylesheet>
