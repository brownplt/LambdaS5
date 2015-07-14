// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 15.4.4.15-2-5
description: >
    Array.prototype.lastIndexOf - 'length' is own data property that
    overrides an inherited accessor property on an Array-like object
includes: [runTestCase.js]
---*/

function testcase() {
        var proto = {};
        Object.defineProperty(proto, "length", {
            get: function () {
                return 0;
            },
            configurable: true
        });

        var Con = function () {};
        Con.prototype = proto;

        var child = new Con();

        Object.defineProperty(child, "length", {
            value: 2,
            configurable: true
        });
        child[1] = null;

        return Array.prototype.lastIndexOf.call(child, null) === 1;
    }
runTestCase(testcase);
// es5id: 15.4.4.15-2-5
