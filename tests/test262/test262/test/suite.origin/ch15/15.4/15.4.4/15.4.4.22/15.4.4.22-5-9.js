// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.22-5-9
description: >
    Array.prototype.reduceRight - 'initialValue' is returned if 'len'
    is 0 and 'initialValue' is present
includes: [runTestCase.js]
---*/

function testcase() {

        var initialValue = 10;
        return initialValue === [].reduceRight(function () { }, initialValue);
    }
runTestCase(testcase);
// es5id: 15.4.4.22-5-9
