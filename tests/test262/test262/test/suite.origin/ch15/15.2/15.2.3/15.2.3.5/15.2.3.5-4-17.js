// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.5-4-17
description: >
    Object.create - own data property in 'Properties' which is not
    enumerable is not defined in 'obj' (15.2.3.7 step 3)
includes: [runTestCase.js]
---*/

function testcase() {

        var props = {};
        Object.defineProperty(props, "prop", {
            value: {},
            enumerable: false
        });
        var newObj = Object.create({}, props);

        return !newObj.hasOwnProperty("prop");
    }
runTestCase(testcase);
// es5id: 15.2.3.5-4-17
