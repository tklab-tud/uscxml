#!/bin/bash

#
# HTTPS support via keypairs:
# uscxml-browser --private-key=uscxml.key --public-key=uscxml.pub
#

openssl req -x509 -sha256 -nodes -newkey rsa:4096 -keyout uscxml.key -out uscxml.pub