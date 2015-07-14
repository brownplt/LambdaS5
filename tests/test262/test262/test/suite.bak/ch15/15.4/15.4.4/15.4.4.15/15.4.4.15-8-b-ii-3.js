// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.15-8-b-ii-3
description: >
    Array.prototype.lastIndexOf - both type of array element and type
    of search element are Null
includes: [runTestCase.js]
---*/

function testcase() {

        return [null].lastIndexOf(null) === 0;
    }
runTestCase(testcase);
// es5id: 15.4.4.15-8-b-ii-3
