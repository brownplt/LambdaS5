// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.8.2.11-1
description: Math.max({}) is NaN
includes: [runTestCase.js]
---*/

function testcase() {
    return isNaN(Math.max({}));
}
runTestCase(testcase);
// es5id: 15.8.2.11-1
