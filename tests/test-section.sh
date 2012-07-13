#!/bin/bash

python test262/hg-262/test262/tools/packaging/test262.py \
  --command ./s5-test262 \
  --tests test262/hg-262/test262/ \
  --full-summary \
  $@
