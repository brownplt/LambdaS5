// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.12.3-4-1
description: >
    JSON.stringify ignores replacer aruguments that are not functions
    or arrays..
includes: [runTestCase.js]
---*/

function testcase() {
  try {
     return JSON.stringify([42],{})=== '[42]';
     }
   catch (e) {return  false}
  }
runTestCase(testcase);
// es5id: 15.12.3-4-1
