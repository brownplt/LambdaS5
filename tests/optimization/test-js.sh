#!/bin/bash

# the file is located in tests/optimization
# always suppose the running directory is in tests

# to see what's passed in, look at
echo "get arguments:" 
echo "$0 $@"

if [ $# -lt 2 ]
then
    echo "$0 <jsfile> <s5-options>"
    exit 1
fi

DIR=`dirname $0`
cd $DIR/..

marshalled=`mktemp -t s5.XXXXXX`
jsfile=$1
shift 1 # to get <s5-options>
options="$@"


# get the es5id
esid=`grep 'es5id' $jsfile | head -n 1 | sed -n 's/.*es5id:[ ]*\(.*\)$/\1/p'`
if [ $esid = "" ]
then
    esid="unknownid"
fi

# run through optimization phases and collect nodes.
# marshal the optimized s5 code to a file for performance.
ocamlrun ../obj/s5.d.byte \
  -desugar $jsfile \
  -internal-env env-vars -apply \
  -env ../envs/es5.env -apply \
  "$@" \
  -save-s5 $marshalled > optimization/id_$esid.optimizeinfo

# load the marshalled file and do evaluation
ocamlrun ../obj/s5.d.byte \
  -load-s5  $marshalled\
  -eval-s5

EX=$?
rm -f $marshalled

exit $EX
