// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
* @name: S15.5.4.12_A2_T1;
* @section: 15.5.4.12;
* @assertion: String.prototype.search (regexp) returns ...;
* @description: Simple search substring inside string;
*/


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S15.5.4.12_A2_T1",

path: "15_Native\15.5_String_Objects\15.5.4_Properties_of_the_String_Prototype_Object\15.5.4.12_String.prototype.search\S15.5.4.12_A2_T1.js",

assertion: "String.prototype.search (regexp) returns ...",

description: "Simple search substring inside string",

test: function testcase() {
   var aString = new String("test string");

//////////////////////////////////////////////////////////////////////////////
//CHECK#1
if (aString.search("string")!== 5) {
  $ERROR('#1: var aString = new String("test string"); aString.search("string")=== 5. Actual: '+aString.search("string"));
}
//
//////////////////////////////////////////////////////////////////////////////

 }
});
