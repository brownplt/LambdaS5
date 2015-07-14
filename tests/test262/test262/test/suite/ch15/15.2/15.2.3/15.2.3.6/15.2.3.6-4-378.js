// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-4-378
description: >
    ES5 Attributes - fail to update [[Writable]] attribute of data
    property ([[Writable]] is false, [[Enumerable]] is false,
    [[Configurable]] is false) to different value
includes: [runTestCase.js]
---*/

function testcase() {
        var obj = {};

        Object.defineProperty(obj, "prop", {
            value: 2010,
            writable: false,
            enumerable: false,
            configurable: false
        });
        var propertyDefineCorrect = obj.hasOwnProperty("prop");
        var desc1 = Object.getOwnPropertyDescriptor(obj, "prop");

        try {
            Object.defineProperty(obj, "prop", {
                writable: true
            });

            return false;
        } catch (e) {
            var desc2 = Object.getOwnPropertyDescriptor(obj, "prop");

            return propertyDefineCorrect && desc1.writable === false && obj.prop === 2010 && desc2.writable === false && e instanceof TypeError;
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.6-4-378
