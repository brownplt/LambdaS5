// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: >
    Check For Statement for automatic semicolon insertion.
    If automatic insertion semicolon would become one of the two semicolons in the header of a For Statement.
    Don`t use semicolons
es5id: 7.9_A6.3_T2
description: For header is (\n \n)
negative: SyntaxError
---*/

//CHECK#1
for(
    
) {
  break;
}
// es5id: S7.9_A6.3_T2
