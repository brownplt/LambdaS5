var x = 5;
function g() {
  var x = 17;
  eval("x = 22;")
  return x === 17;
}
if (g() && window.x === 22) {
  console.log("Passed");
}