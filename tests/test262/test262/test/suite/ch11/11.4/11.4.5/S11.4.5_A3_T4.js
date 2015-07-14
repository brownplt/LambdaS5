// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Operator --x returns x = ToNumber(x) - 1
es5id: 11.4.5_A3_T4
description: Type(x) is undefined or null
---*/

//CHECK#1
var x; 
--x;
if (isNaN(x) !== true) {
  $ERROR('#1: var x; --x; x === Not-a-Number. Actual: ' + (x));
}

//CHECK#2
var x = null; 
--x;
if (x !== -1) {
  $ERROR('#2: var x = null; --x; x === -1. Actual: ' + (x));
}
// es5id: S11.4.5_A3_T4
