// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Operator x >>> y returns ToNumber(x) >>> ToNumber(y)
es5id: 11.7.3_A3_T2.4
description: >
    Type(x) is different from Type(y) and both types vary between
    Number (primitive or object) and Undefined
---*/

//CHECK#1
if (1 >>> undefined !== 1) {
  $ERROR('#1: 1 >>> undefined === 1. Actual: ' + (1 >>> undefined));
}

//CHECK#2
if (undefined >>> 1 !== 0) {
  $ERROR('#2: undefined >>> 1 === 0. Actual: ' + (undefined >>> 1));
}

//CHECK#3
if (new Number(1) >>> undefined !== 1) {
  $ERROR('#3: new Number(1) >>> undefined === 1. Actual: ' + (new Number(1) >>> undefined));
}

//CHECK#4
if (undefined >>> new Number(1) !== 0) {
  $ERROR('#4: undefined >>> new Number(1) === 0. Actual: ' + (undefined >>> new Number(1)));
}
// es5id: S11.7.3_A3_T2.4
