#!/usr/bin/env bash
cd "$(dirname "$0")" || exit

docker run -i \
-v $PWD:/buildFolder todoDefineDockerImage \
bash \
-c "cd /buildFolder && ls -l && ./build.sh" \
--rm