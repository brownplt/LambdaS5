// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 10.6-12-2
description: arguments.callee has correct attributes
includes: [runTestCase.js]
---*/

function testcase() {
  
  var desc = Object.getOwnPropertyDescriptor(arguments,"callee");
  if(desc.configurable === true &&
     desc.enumerable === false &&
     desc.writable === true &&
     desc.hasOwnProperty('get') == false &&
     desc.hasOwnProperty('put') == false)
    return true;   
 }
runTestCase(testcase);
// es5id: 10.6-12-2
