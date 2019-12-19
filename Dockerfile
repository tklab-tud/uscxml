FROM ubuntu:18.04

RUN apt-get update && apt-get install -y \
	git \
    clang \
    cmake

COPY . /tmp/uscxml

RUN cd /tmp/uscxml \
    && mkdir build-docker-release && cd build-docker-release \
    && cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_BUILD_TYPE=release .. \
    && cmake --build . \
    && mv bin/uscxml-browser /usr/bin/uscxml-browser \
    && mv bin/uscxml-transform /usr/bin/uscxml-transform \
	&& rm -rf /tmp/uscxml