#!/bin/bash
python ./etc/build/gen_build.py | ninja -f /dev/stdin
