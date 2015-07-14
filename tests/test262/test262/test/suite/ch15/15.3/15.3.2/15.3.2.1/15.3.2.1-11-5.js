// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.3.2.1-11-5
description: >
    Duplicate combined parameter name in Function constructor allowed
    if body is not strict
includes: [runTestCase.js]
---*/

function testcase()
{   
    Function('a,a','return;');
    return true;
 }
runTestCase(testcase);
// es5id: 15.3.2.1-11-5
