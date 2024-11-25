#!/bin/bash

set -e
rm -rf setup && mkdir setup
cd setup

git clone https://github.com/emp-toolkit/emp-tool.git
cd emp-tool
cmake . -DCMAKE_INSTALL_PREFIX=../
make -j
make install
cd ..

git clone https://github.com/emp-toolkit/emp-ot.git
cd emp-ot
cmake . -DCMAKE_INSTALL_PREFIX=../
make -j
make install
cd ..

cd ..