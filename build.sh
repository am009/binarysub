#!/bin/sh

g++-12 -g --std=c++2b ./binarysub.cpp -c -o binarysub.o && \
g++-12 -g --std=c++2b ./demo.cpp binarysub.o -o binarysub && \
./binarysub
