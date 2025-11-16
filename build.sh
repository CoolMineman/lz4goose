
# If both scripts run in the same directory they step on eachother's toes
cd etc/build && (python gen_build_goose.py | ninja -f /dev/stdin) && cd ../.. &&
(python ./etc/build/gen_build.py | ninja -f /dev/stdin)