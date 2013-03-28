#!/bin/bash
wget -rl1 http://www.w3.org/Voice/2013/scxml-irp/
find ./www.w3.org -name *.txml -exec cp {} ./txml \;
rm -rf www.w3.org