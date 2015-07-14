// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 10.4.2-2-c-1
description: >
    Direct val code in non-strict mode - can instantiate variable in
    calling context
includes: [runTestCase.js]
---*/

function testcase() {
  var x = 0;
  return function inner() {
     var x = 1;
     if (x === 1)
        return true;
     } ();
   }

runTestCase(testcase);
// es5id: 10.4.2-2-c-1
