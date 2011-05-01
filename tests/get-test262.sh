#!/bin/bash

wget -O test262.tgz http://hg.ecmascript.org/tests/test262/archive/tip.tar.gz
tar xzf test262.tgz --directory=./test262
cp -r ./test262/test262-*/* ./test262/test262/
rm -rf ./test262/test262-*

