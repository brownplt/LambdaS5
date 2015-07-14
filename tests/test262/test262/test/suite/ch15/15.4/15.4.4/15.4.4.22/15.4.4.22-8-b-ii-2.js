// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.22-8-b-ii-2
description: >
    Array.prototype.reduceRight - deleted properties in step 2 are
    visible here
includes: [runTestCase.js]
---*/

function testcase() {

        var obj = { 2: "accumulator", 3: "another" };

        Object.defineProperty(obj, "length", {
            get: function () {
                delete obj[2];
                return 5;
            },
            configurable: true
        });

        return "accumulator" !== Array.prototype.reduceRight.call(obj, function () { });
    }
runTestCase(testcase);
// es5id: 15.4.4.22-8-b-ii-2
