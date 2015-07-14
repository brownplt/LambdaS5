// Copyright 2011 Google Inc.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/*---
es5id: 13.2_A7_T1
description: check if "caller" poisoning poisons  hasOwnProperty too
flags: [onlyStrict]
---*/

"use strict";
(function(){}).hasOwnProperty('caller');
// es5id: S13.2_A7_T1
