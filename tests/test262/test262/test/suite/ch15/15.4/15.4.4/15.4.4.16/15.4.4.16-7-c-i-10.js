// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.16-7-c-i-10
description: >
    Array.prototype.every - element to be retrieved is own accessor
    property on an Array
includes: [runTestCase.js]
---*/

function testcase() {

        function callbackfn(val, idx, obj) {
            if (idx === 2) {
                return val !== 12;
            } else {
                return true;
            }
        }

        var arr = [];

        Object.defineProperty(arr, "2", {
            get: function () {
                return 12;
            },
            configurable: true
        });

        return !arr.every(callbackfn);
    }
runTestCase(testcase);
// es5id: 15.4.4.16-7-c-i-10
