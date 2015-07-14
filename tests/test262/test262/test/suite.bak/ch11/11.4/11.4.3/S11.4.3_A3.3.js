// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Result of applying "typeof" operator to boolean is "boolean"
es5id: 11.4.3_A3.3
description: typeof (boolean value) === "boolean"
---*/

//CHECK#1
if (typeof true !== "boolean") {
  $ERROR('#1: typeof true === "boolean". Actual: ' + (typeof true));
}

//CHECK#2
if (typeof false !== "boolean") {
  $ERROR('#2: typeof false === "boolean". Actual: ' + (typeof false));
}

//CHECK#3
if (typeof !-1 !== "boolean") {
  $ERROR('#3: typeof !-1 === "boolean". Actual: ' + (typeof !-1));
}
// es5id: S11.4.3_A3.3
