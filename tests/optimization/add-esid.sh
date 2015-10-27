#!/bin/sh

# the file is located in tests/optimization
# always suppose the running directory is in tests

DIR=`dirname $0`
cd $DIR/..


jsfiles=`find test262/test262/test/suite/ch* -name '*.js'`

for js in $jsfiles
do
    echo "add $js"
    file=$(basename $js)
    id=${file%%.js}
    echo "// es5id: $id" >> $js
done
