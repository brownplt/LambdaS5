// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    ToNumber(first expression) is called first, and then ToNumber(second
    expression)
es5id: 11.5.3_A2.3_T1
description: Checking with "throw"
---*/

//CHECK#1
var x = { valueOf: function () { throw "x"; } };
var y = { valueOf: function () { throw "y"; } };
try {
   x % y;
   $ERROR('#1.1: var x = { valueOf: function () { throw "x"; } }; var y = { valueOf: function () { throw "y"; } }; x % y throw "x". Actual: ' + (x % y));
} catch (e) {
   if (e === "y") {
     $ERROR('#1.2: ToNumber(first expression) is called first, and then ToNumber(second expression)');
   } else {
     if (e !== "x") {
       $ERROR('#1.3: var x = { valueOf: function () { throw "x"; } }; var y = { valueOf: function () { throw "y"; } }; x % y throw "x". Actual: ' + (e));
     }
   }
}
// es5id: S11.5.3_A2.3_T1
