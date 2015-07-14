// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.7-5-b-223
description: >
    Object.defineProperties - value of 'get' property of 'descObj' is
    a function (8.10.5 step 7.b)
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = {};

        var getter = function () {
            return 100;
        };

        Object.defineProperties(obj, {
            property: {
                get: getter
            }
        });

        return obj.property === 100;
    }
runTestCase(testcase);
// es5id: 15.2.3.7-5-b-223
