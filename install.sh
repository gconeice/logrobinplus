#!/bin/bash

set -e
rm -rf build && mkdir build
cd build

CC=clang CXX=clang++ cmake ../ -DCMAKE_PREFIX_PATH=$PWD/../setup/ && make -j && mkdir data

cd ..