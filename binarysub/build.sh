#!/bin/sh

SOURCES="./binarysub.cpp ./binarysub-core.cpp"

g++-12 -g --std=c++2b -fno-rtti $SOURCES ./demo.cpp -o binarysub && \
./binarysub
