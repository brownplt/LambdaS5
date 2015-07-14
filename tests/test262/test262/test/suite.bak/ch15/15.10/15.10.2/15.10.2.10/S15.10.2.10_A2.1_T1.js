// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: "CharacterEscape :: c ControlLetter"
es5id: 15.10.2.10_A2.1_T1
description: "ControlLetter :: A - Z"
---*/

//CHECK#0041-005A
var result = true; 
for (alpha = 0x0041; alpha <= 0x005A; alpha++) {
  str = String.fromCharCode(alpha % 32);
  arr = (new RegExp("\\c" + String.fromCharCode(alpha))).exec(str);  
  if ((arr === null) || (arr[0] !== str)) {
    result = false;
  }
}

if (result !== true) {
  $ERROR('#1: CharacterEscape :: c A - Z');
}
// es5id: S15.10.2.10_A2.1_T1
