// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.3-3-10
description: Object.getOwnPropertyDescriptor - 'P' is not an existing property
includes: [runTestCase.js]
---*/

function testcase() {

        var obj = {
            property: "ownDataProperty"
        };

        var desc = Object.getOwnPropertyDescriptor(obj, "propertyNonExist");

        return typeof desc === "undefined";
    }
runTestCase(testcase);
// es5id: 15.2.3.3-3-10
