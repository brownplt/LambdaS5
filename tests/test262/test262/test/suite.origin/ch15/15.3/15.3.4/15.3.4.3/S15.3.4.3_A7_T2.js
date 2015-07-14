// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    If argArray is either an array or an arguments object,
    the function is passed the (ToUint32(argArray.length)) arguments argArray[0], argArray[1],...,argArray[ToUint32(argArray.length)-1]
es5id: 15.3.4.3_A7_T2
description: argArray is (null,[1,2,3])
---*/

new Function("a1,a2","a3","this.shifted=a2;").apply(null,[1,2,3]);

//CHECK#1
if (this["shifted"] !== 2) {
  $ERROR('#1: If argArray is either an array or an arguments object, the function is passed the...');
}
// es5id: S15.3.4.3_A7_T2
