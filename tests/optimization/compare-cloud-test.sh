#!/bin/sh

if [ $# -lt 1 ]
then
    echo "$0 <optimized-output-directory>"
    exit 1
fi

optimizeddir=`pwd`/$1

# change directory to tests/
DIR=`dirname $0`
cd $DIR/..
base=non-optimized-test-result

# tricky to get result file without path prefix
cd $base
nonoptdir=`pwd`
resultfiles=`find . -name '*.result'`
cd ..

for result in $resultfiles 
do
    nonoptfile=$nonoptdir/$result
    optimizedfile=$optimizeddir/$result
    filename=$(basename $nonoptfile)
    file=${filename%.result}
    echo "compare non-opt and opt $file"
    diff $nonoptfile $optimizedfile
done
