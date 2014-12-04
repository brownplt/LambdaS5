#!/bin/bash

python test262/test262/tools/packaging/test262.py \
  --command ./s5-optimization-test262 \
  --tests test262/test262/ \
  --full-summary \
  $@
