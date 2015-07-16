// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: String.prototype.toLocaleLowerCase()
es5id: 15.5.4.17_A1_T3
description: Checking by using eval
---*/

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if ("BJ".toLocaleLowerCase() !== "bj") {
  $ERROR('#1: eval("\\"BJ\\"").toLocaleLowerCase() === "bj". Actual: '+"BJ".toLocaleLowerCase() );
}
//
//////////////////////////////////////////////////////////////////////////////
// es5id: S15.5.4.17_A1_T3
