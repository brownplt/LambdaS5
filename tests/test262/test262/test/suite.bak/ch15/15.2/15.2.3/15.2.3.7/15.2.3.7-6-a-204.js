// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.7-6-a-204
description: >
    Object.defineProperties - 'O' is an Array, 'P' is an array index
    named property, 'P' property doesn't exist in 'O', test
    [[Configurable]] of 'P' property in 'Attributes' is set as false
    value if [[Configurable]] is absent in accessor descriptor 'desc'
    (15.4.5.1 step 4.c)
includes: [runTestCase.js]
---*/

function testcase() {
        var arr = [];
        var beforeDeleted = false;
        var afterDeleted = false;
        arr.verifySetter = 100;

        Object.defineProperties(arr, {
            "0": {
                set: function (value) {
                    arr.verifySetter = value;
                },
                get: function () {
                    return arr.verifySetter;
                },
                enumerable: true
            }
        });

        beforeDeleted = arr.hasOwnProperty("0");
        delete arr[0];
        afterDeleted = arr.hasOwnProperty("0");

        arr[0] = 101;

        return beforeDeleted && afterDeleted && arr[0] === 101 && arr.verifySetter === 101;
    }
runTestCase(testcase);
// es5id: 15.2.3.7-6-a-204
