var x = 198;
eval("var x = 222");
if (x === 198) {
  console.log("Passed");
}

var y = 211;
eval("y = 233");
if (y === 233) {
  console.log("Passed");
}