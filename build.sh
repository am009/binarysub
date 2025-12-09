#!/bin/sh

SOURCES="binarysub/binarysub.cpp binarysub/binarysub-core.cpp binarysub/simplesub-infer.cpp binarysub/simplesub-parser.cpp"

g++-12 -g --std=c++2b -fno-rtti $SOURCES binarysub/simplesub-test.cpp -o build/binarysub && \
./build/binarysub
