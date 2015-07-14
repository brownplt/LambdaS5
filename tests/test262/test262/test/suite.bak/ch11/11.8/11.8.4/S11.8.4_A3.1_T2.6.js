// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    If Type(Primitive(x)) is not String or Type(Primitive(y)) is not String,
    then operator x >= y returns ToNumber(x) >= ToNumber(y)
es5id: 11.8.4_A3.1_T2.6
description: >
    Type(Primitive(x)) is different from Type(Primitive(y)) and both
    types vary between String (primitive or object) and Undefined
---*/

//CHECK#1
if ("1" >= undefined !== false) {
  $ERROR('#1: "1" >= undefined === false');
}

//CHECK#2
if (undefined >= "1" !== false) {
  $ERROR('#2: undefined >= "1" === false');
}

//CHECK#3
if (new String("1") >= undefined !== false) {
  $ERROR('#3: new String("1") >= undefined === false');
}

//CHECK#4
if (undefined >= new String("1") !== false) {
  $ERROR('#4: undefined >= new String("1") === false');
}
// es5id: S11.8.4_A3.1_T2.6
