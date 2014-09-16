#!/bin/sh

file=`pwd`/t.js

cd ..
./s5.d.byte -desugar $file -print-src -env ../envs/es5.env -apply -eval
