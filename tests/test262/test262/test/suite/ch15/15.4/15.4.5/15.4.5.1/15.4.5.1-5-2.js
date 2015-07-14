// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.5.1-5-2
description: >
    Defining a property named 4294967295 (2**32-1) doesn't change
    length of the array
includes: [runTestCase.js]
---*/

function testcase() {  
  var a =[0,1,2];
  a[4294967295] = "not an array element" ;
  return a.length===3;
 }
runTestCase(testcase);
// es5id: 15.4.5.1-5-2
