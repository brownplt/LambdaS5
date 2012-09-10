var x = [];
var y = ["zero", "one", "two"];
x.push.apply(x, y);
if (x.length === 5) {
  console.log("passed");
}