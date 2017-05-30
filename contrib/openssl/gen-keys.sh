#!/bin/bash

openssl req -x509 -sha256 -nodes -newkey rsa:4096 -keyout uscxml.key -out uscxml.cert