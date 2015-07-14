// Copyright (c) 2012 Ecma International.  All rights reserved.
// Ecma International makes this code available under the terms and conditions set
// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the
// "Use Terms").   Any redistribution of this code must retain the above
// copyright and this notice and otherwise comply with the Use Terms.

/*---
es5id: 10.4.3-1-100gs
description: >
    Strict Mode - checking 'this' (strict function passed as arg to
    String.prototype.replace from non-strict context)
flags: [onlyStrict]
---*/

var x = 3;

function f() {
    "use strict";
    x = this;
    return "a";
}
if (("ab".replace("b", f)!=="aa") || (x!==undefined)) {
        throw "'this' had incorrect value!";
}
// es5id: 10.4.3-1-100gs
