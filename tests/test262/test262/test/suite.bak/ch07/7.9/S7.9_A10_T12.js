// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Check {} for automatic semicolon insertion
es5id: 7.9_A10_T12
description: "Checking if execution of \"{ \\n a: \\n 1 \\n } \\n 3\" passes"
---*/

//CHECK#1
{
a:
1 
} 
3
// es5id: S7.9_A10_T12
