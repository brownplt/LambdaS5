// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Blocks within "for" braces are not allowed
es5id: 12.6.3_A8_T2
description: >
    Checking if execution of "for(index=0; {index++;index<100;};
    index*2;) {  arr.add(""+index);}" fails
negative: SyntaxError
---*/

var arr = [];

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
for(index=0; {index++;index<100;}; index*2;) {	arr.add(""+index);};
//
//////////////////////////////////////////////////////////////////////////////
// es5id: S12.6.3_A8_T2
