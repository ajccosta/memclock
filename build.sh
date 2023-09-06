#!/bin/bash
./autogen.sh
./configure --disable-extstore
make -j
