// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.17-7-c-i-30
description: >
    Array.prototype.some - unhandled exceptions happened in getter
    terminate iteration on an Array-like object
includes: [runTestCase.js]
---*/

function testcase() {

        var accessed = false;
        function callbackfn(val, idx, obj) {
            if (idx > 1) {
                accessed = true;
            }
            return true;
        }

        var obj = { length: 20 };
        Object.defineProperty(obj, "1", {
            get: function () {
                throw new RangeError("unhandle exception happened in getter");
            },
            configurable: true
        });

        try {
            Array.prototype.some.call(obj, callbackfn);
            return false;
        } catch (ex) {
            return ex instanceof RangeError && !accessed;
        }
    }
runTestCase(testcase);
// es5id: 15.4.4.17-7-c-i-30
