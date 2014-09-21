#!/bin/bash

#########NOTE###########
# don't pass quoted into to -count-nodes. it does not work.
# ./test-section.sh strict ch07 -count-nodes "non optimized file node count"
# try to change it to
# ./test-section.sh strict ch07 -count-nodes non-optimized-file-node-count

# the file is located in tests/optimization
# always suppose the running directory is in tests
if [ -x $2 ]
then
    echo "$0 <strict|nonstrict> <ch07|ch08..|ch15> <s5-options>"
    exit 1
fi

DIR=`dirname $0`
cd $DIR/..

if [ $1 = "strict" ]
then
    strict=--strict_only
elif [ $1 = "nonstrict" ]
then
    strict=--non_strict_only
else
    echo "$1 should be either 'strict' or 'nonstrict'"
    exit 1
fi

section=$2
shift 2
options="$@"

# s5 script that will accept js filename and 
# optimization options

runs5_script=optimization/test-js.sh

cmd="$runs5_script {{path}} $@"

python test262/test262/tools/packaging/test262.py \
  --command "$cmd" \
  --tests test262/test262/ \
  --full-summary \
  $strict \
  $section
