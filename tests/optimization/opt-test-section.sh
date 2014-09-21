#!/bin/bash

# the file is located in tests/optimization
# always suppose the running directory is in tests

DIR=`dirname $0`
cd $DIR/..

python test262/test262/tools/packaging/test262.py \
  --command optimization/opt-s5-test262 \
  --tests test262/test262/ \
  --full-summary \
  $@
