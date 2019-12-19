#!/bin/bash
cd "$(dirname "$0")" || exit

cmake -Bbuild-docker-release2 -DCMAKE_BUILD_TYPE=release -S.
cmake --build ./build-docker-release2   -- -j 10