// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.5-4-310
description: >
    Object.create - [[Get]] is set as undefined if it is absent in
    accessor descriptor of one property in 'Properties' (8.12.9 step
    4.b)
includes: [runTestCase.js]
---*/

function testcase() {
        var newObj = Object.create({}, {
            prop: {
                set: function () { },
                enumerable: true,
                configurable: true
            }
        });
        return newObj.hasOwnProperty("prop") && newObj.prop === undefined;
    }
runTestCase(testcase);
// es5id: 15.2.3.5-4-310
