// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: The length property of eval has the attribute DontDelete
es5id: 15.1.2.1_A4.2
description: Checking use hasOwnProperty, delete
includes: [$FAIL.js]
---*/

//CHECK#1
if (eval.hasOwnProperty('length') !== true) {
  $FAIL('#1: eval.hasOwnProperty(\'length\') === true. Actual: ' + (eval.hasOwnProperty('length')));
}

delete eval.length;

//CHECK#2
if (eval.hasOwnProperty('length') !== true) {
  $ERROR('#2: delete eval.length; eval.hasOwnProperty(\'length\') === true. Actual: ' + (eval.hasOwnProperty('length')));
}

//CHECK#3
if (eval.length === undefined) {
  $ERROR('#3: delete eval.length; eval.length !== undefined');
}
// es5id: S15.1.2.1_A4.2
