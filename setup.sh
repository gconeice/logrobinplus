#!/bin/bash

set -e
rm -rf setup && mkdir setup
cd setup

git clone https://github.com/emp-toolkit/emp-tool.git
cd emp-tool
cmake . -DCMAKE_INSTALL_PREFIX=../
if  [[ $1 = "-para" ]]; then
    make -j
else
    make
fi    
make install
cd ..

git clone https://github.com/emp-toolkit/emp-ot.git
cd emp-ot
cmake . -DCMAKE_INSTALL_PREFIX=../
if  [[ $1 = "-para" ]]; then
    make -j
else
    make
fi   
make install
cd ..

cd ..