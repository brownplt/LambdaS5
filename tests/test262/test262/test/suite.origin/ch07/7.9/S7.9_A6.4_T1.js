// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
info: Check For Statement for automatic semicolon insertion
es5id: 7.9_A6.4_T1
description: >
    Three semicolons. For header is (false semicolon false semicolon
    false semicolon)
negative: SyntaxError
---*/

//CHECK#1
for(false;false;false;) {
  break;
}
// es5id: S7.9_A6.4_T1
