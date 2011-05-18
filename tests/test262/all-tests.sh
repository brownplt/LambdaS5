#!/bin/bash

BASEDIR=.
TESTDIR=$BASEDIR/test262/test/suite

IETESTS=$TESTDIR/ietestcenter
SPUTNIKTESTS=$TESTDIR/sputnik_converted

EVALERRS=0
PARSERRS=0
PROGERRS=0
TESTERRS=0
UNKNOWN=0
TESTWIN=0
TOTAL=0

function singleTest {
    echo "total tests: $TOTAL"
    echo "parse errs: $EVALERRS"
    echo "eval errs: $PARSERRS"
    echo "prog errs: $PROGERRS"
    echo "failed: $TESTERRS"
    echo "unknown: $UNKNOWN"
    echo "test: $TESTWIN"
    echo $1
    $BASEDIR/single-test.sh $1
    RESULT=$?
    echo $RESULT
    if [ $RESULT -eq 5 ]; then
        UNKNOWN=$(($UNKNOWN+1))
    elif [ $RESULT -eq 4 ]; then
        TESTERRS=$(($TESTERRS+1))
    elif [ $RESULT -eq 3 ]; then
        EVALERRS=$(($EVALERRS+1))
    elif [ $RESULT -eq 2 ]; then
        PARSERRS=$(($PARSERRS+1))
    elif [ $RESULT -eq 1 ]; then
        PROGERRS=$(($PROGERRS+1))
    elif [ $RESULT -eq 0 ]; then
        TESTWIN=$(($TESTWIN+1))
    fi
    TOTAL=$(($TOTAL+1))
}

function testDir {
    echo "total tests: $TOTAL"
    echo "parse errs: $EVALERRS"
    echo "eval errs: $PARSERRS"
    echo $1
    for file in $(find $1 -name "*.js"); do
        singleTest $file
    done
}

testDir $SPUTNIKTESTS
testDir $IETESTS

echo "total tests: $TOTAL"
echo "parse errs: $EVALERRS"
echo "eval errs: $PARSERRS"
echo "prog errs: $PROGERRS"
echo "failed: $TESTERRS"
echo "unknown: $UNKNOWN"
echo "test: $TESTWIN"


