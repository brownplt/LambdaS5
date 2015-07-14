// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    When "instanceof" returns true it means that
    GetValue(RelationalExpression) is constructed with ShiftExpression
es5id: 11.8.6_A7_T1
description: Checking Object object
---*/

var __obj={};

//CHECK#1
if (!(__obj instanceof Object)) {
	$ERROR('#1: If instanceof returns true then GetValue(RelationalExpression) was constructed with ShiftExpression');
}

//CHECK#2
if (__obj.constructor !== Object) {
	$ERROR('#2: If instanceof returns true then GetValue(RelationalExpression) was constructed with ShiftExpression');
}
// es5id: S11.8.6_A7_T1
