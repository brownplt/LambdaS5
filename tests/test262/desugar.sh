#!/bin/bash

echo $1 > file2.js
cat $1 > file.js

../../bin/js -e "print(JSON.stringify(Reflect.parse(read('$1'),{loc:true}),function(key,value){if(key==='value'&&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2))"
