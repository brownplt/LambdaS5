// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.16-7-c-i-5
description: >
    Array.prototype.every - element to be retrieved is own data
    property that overrides an inherited accessor property on an
    Array-like object
includes: [runTestCase.js]
---*/

function testcase() {

        function callbackfn(val, idx, obj) {
            if (idx === 0) {
                return val === 5;
            } else {
                return true;
            }
        }

        var proto = {};

        Object.defineProperty(proto, "0", {
            get: function () {
                return 5;
            },
            configurable: true
        });

        var Con = function () { };
        Con.prototype = proto;

        var child = new Con();
        child.length = 2;
        Object.defineProperty(child, "0", {
            value: 11,
            configurable: true
        });
        child[1] = 12;

        return !Array.prototype.every.call(child, callbackfn);
    }
runTestCase(testcase);
// es5id: 15.4.4.16-7-c-i-5
