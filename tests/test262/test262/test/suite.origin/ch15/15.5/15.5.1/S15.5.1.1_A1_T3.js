// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    When String is called as a function rather than as a constructor, it
    performs a type conversion
es5id: 15.5.1.1_A1_T3
description: Call String(void 0)
---*/

var __str = String(void 0);

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if (typeof __str !== "string") {
  $ERROR('#1: __str = String(void 0); typeof __str === "string". Actual: typeof __str ==='+typeof __str ); 
}
//
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//CHECK#2
if (__str !== "undefined") {
  $ERROR('#2: __str = String(void 0); __str === "undefined". Actual: __str ==='+__str ); 
}
//
//////////////////////////////////////////////////////////////////////////////
// es5id: S15.5.1.1_A1_T3
