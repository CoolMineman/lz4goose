mkdir etc/build/gen
python etc/build/gen_build_goose.py > etc/build/gen/goose.ninja &&
ninja -f etc/build/gen/goose.ninja &&
python ./etc/build/gen_build.py > etc/build/gen/build.ninja && 
ninja -f etc/build/gen/build.ninja