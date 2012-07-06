var x;

var g = Object.getOwnPropertyDescriptor(this, "x");
console.log(this);
if(g.value === undefined && g.writable === true && g.configurable === true && g.enumerable === true) {
  print('Passed!');
}
