// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Operator x >>> y returns ToNumber(x) >>> ToNumber(y)
es5id: 11.7.3_A3_T1.4
description: Type(x) and Type(y) vary between Null and Undefined
---*/

//CHECK#1
if (null >>> undefined !== 0) {
  $ERROR('#1: null >>> undefined === 0. Actual: ' + (null >>> undefined));
}

//CHECK#2
if (undefined >>> null !== 0) {
  $ERROR('#2: undefined >>> null === 0. Actual: ' + (undefined >>> null));
}

//CHECK#3
if (undefined >>> undefined !== 0) {
  $ERROR('#3: undefined >>> undefined === 0. Actual: ' + (undefined >>> undefined));
}

//CHECK#4
if (null >>> null !== 0) {
  $ERROR('#4: null >>> null === 0. Actual: ' + (null >>> null));
}
// es5id: S11.7.3_A3_T1.4
