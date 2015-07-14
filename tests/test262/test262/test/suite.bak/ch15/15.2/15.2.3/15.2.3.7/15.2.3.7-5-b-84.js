// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.7-5-b-84
description: >
    Object.defineProperties - 'descObj' is the global object which
    implements its own [[Get]] method to get 'configurable' property
    (8.10.5 step 4.a)
includes:
    - runTestCase.js
    - fnGlobalObject.js
---*/

function testcase() {

        var obj = {};

        try {
            fnGlobalObject().configurable = true;

            Object.defineProperties(obj, {
                prop: fnGlobalObject()
            });

            var result1 = obj.hasOwnProperty("prop");
            delete obj.prop;
            var result2 = obj.hasOwnProperty("prop");

            return result1 === true && result2 === false;
        } finally {
            delete fnGlobalObject().configurable;
        }
    }
runTestCase(testcase);
// es5id: 15.2.3.7-5-b-84
