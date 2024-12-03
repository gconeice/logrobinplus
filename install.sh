#!/bin/bash

set -e
rm -rf build && mkdir build
cd build

CC=clang CXX=clang++ cmake ../ -DCMAKE_PREFIX_PATH=$PWD/../setup/
if  [[ $1 = "-para" ]]; then
    make -j && mkdir data
else
    make && mkdir data
fi

cd ..