// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.16-7-c-iii-29
description: >
    Array.prototype.every - return value (new Boolean(false)) of
    callbackfn is treated as true value
includes: [runTestCase.js]
---*/

function testcase() {

        var accessed = false;

        function callbackfn(val, idx, obj) {
            accessed = true;
            return new Boolean(false);
        }

        return [11].every(callbackfn) && accessed;
    }
runTestCase(testcase);
// es5id: 15.4.4.16-7-c-iii-29
