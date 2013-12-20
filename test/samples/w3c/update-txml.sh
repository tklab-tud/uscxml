#!/bin/bash
wget -rl1 -Atxml,txt,xsl http://www.w3.org/Voice/2013/scxml-irp/

find ./www.w3.org -name "*.txml" -exec cp {} ./txml \;
find ./www.w3.org -name "*.txt" -exec cp {} ./txml \;
find ./www.w3.org -name "*.xsl" -exec cp {} . \;
rm -rf www.w3.org