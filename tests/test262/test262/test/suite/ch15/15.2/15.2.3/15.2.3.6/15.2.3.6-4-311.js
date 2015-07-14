// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.2.3.6-4-311
description: >
    Object.defineProperty - 'O' is an Arguments object, 'name' is an
    index named accessor property of 'O' but not defined in
    [[ParameterMap]] of 'O', test TypeError is thrown when updating
    the [[Enumerable]] attribute value of 'name' which is not
    configurable (10.6 [[DefineOwnProperty]] step 4)
includes:
    - runTestCase.js
    - accessorPropertyAttributesAreCorrect.js
---*/

function testcase() {
        return (function () {
            function getFunc() {
                return 0;
            }
            Object.defineProperty(arguments, "0", {
                get: getFunc,
                enumerable: true,
                configurable: false
            });
            try {
                Object.defineProperty(arguments, "0", {
                    enumerable: false
                });
            } catch (e) {
                return e instanceof TypeError && accessorPropertyAttributesAreCorrect(arguments, "0", getFunc, undefined, undefined, true, false);
            }
            return false;
        }());
    }
runTestCase(testcase);
// es5id: 15.2.3.6-4-311
