"use strict";
var r;
var n;
Object.defineProperty(Number.prototype, "x", { "set" : function (v) { n = v; }, "enumerable" : true, "configurable" : true });
r = 1["x"]; // undefined
if (r === undefined) {
  print("Passed!");
}
