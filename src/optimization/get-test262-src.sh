#!/bin/sh

tests=~/github/LambdaS5/tests
python $tests/test262/test262/tools/packaging/test262.py  --tests $tests/test262/test262/ --command dummy --cat $1
