// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.18-3-21
description: >
    Array.prototype.forEach - 'length' is an object that has an own
    valueOf method that returns an object and toString method that
    returns a string
includes: [runTestCase.js]
---*/

function testcase() {

        var testResult = false;
        var firstStepOccured = false;
        var secondStepOccured = false;

        function callbackfn(val, idx, obj) {
            testResult = (val > 10);
        }

        var obj = {
            1: 11,
            2: 9,
            length: {
                valueOf: function () {
                    firstStepOccured = true;
                    return {};
                },
                toString: function () {
                    secondStepOccured = true;
                    return '2';
                }
            }
        };

        Array.prototype.forEach.call(obj, callbackfn);

        return testResult && firstStepOccured && secondStepOccured;
    }
runTestCase(testcase);
// es5id: 15.4.4.18-3-21
