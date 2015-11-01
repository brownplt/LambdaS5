#!/bin/bash

BASE_PATH=`dirname $0`/..

$BASE_PATH/bin/js -e "print(JSON.stringify(Reflect.parse(read('$1'),{loc:true}),function(key,value){if(key==='value'&&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2))"
exit $?
