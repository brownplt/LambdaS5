// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-4-273
description: >
    Object.defineProperty - 'O' is an Array, 'name' is an array index
    named property, name is accessor property and 'desc' is accessor
    descriptor, test updating multiple attribute values of 'name'
    (15.4.5.1 step 4.c)
includes:
    - runTestCase.js
    - accessorPropertyAttributesAreCorrect.js
---*/

function testcase() {

        var arrObj = [];

        function setFunc(value) {
            arrObj.setVerifyHelpProp = value;
        }
        function getFunc() {
            return 12;
        }
        Object.defineProperty(arrObj, "1", {
            get: function () {
                return 6;
            },
            set: setFunc,
            enumerable: true,
            configurable: true
        });

        Object.defineProperty(arrObj, "1", {
            get: getFunc,
            enumerable: false,
            configurable: false
        });
        return accessorPropertyAttributesAreCorrect(arrObj, "1", getFunc, setFunc, "setVerifyHelpProp", false, false);
    }
runTestCase(testcase);
// es5id: 15.2.3.6-4-273
