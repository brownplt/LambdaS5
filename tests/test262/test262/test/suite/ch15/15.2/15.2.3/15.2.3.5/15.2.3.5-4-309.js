// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.5-4-309
description: >
    Object.create - [[Configurable]] is set as false if it is absent
    in data descriptor of one property in 'Properties' (8.12.9 step
    4.a.i)
includes: [runTestCase.js]
---*/

function testcase() {
        var isNotConfigurable = false;

        try {
            var newObj = Object.create({}, {
                prop: {
                    value: 1001,
                    writable: true,
                    enumerable: true
                }
            });
            var hasProperty = newObj.hasOwnProperty("prop");
            delete newObj.prop;
            isNotConfigurable = newObj.hasOwnProperty("prop");
            return hasProperty && isNotConfigurable;
        } catch (e) {
            return false;
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.5-4-309
