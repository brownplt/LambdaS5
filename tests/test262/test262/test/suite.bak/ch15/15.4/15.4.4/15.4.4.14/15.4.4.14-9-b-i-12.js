// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.14-9-b-i-12
description: >
    Array.prototype.indexOf - element to be retrieved is own accessor
    property that overrides an inherited data property on an
    Array-like object
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = { length: 1 };

        try {
            Object.prototype[0] = false;
            Object.defineProperty(obj, "0", {
                get: function () {
                    return true;
                },
                configurable: true
            });

            return 0 === Array.prototype.indexOf.call(obj, true);
        } finally {
            delete Object.prototype[0];
        }
    }
runTestCase(testcase);
// es5id: 15.4.4.14-9-b-i-12
