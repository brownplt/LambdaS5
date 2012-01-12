@echo off
echo %1 > file2.js
cat %1 > file.js

set fname=%1
set fname=%fname:\=\\%
echo print(JSON.stringify(Reflect.parse(read("%fname%"),{loc:true,source:"%fname%"}),function(key,value) {if (key==='value'^&^&(value)instanceof(RegExp)){return{re_lit:String(value)}}return(value)},2)); > c3driver.js

..\bin\jstest.exe c3driver.js
