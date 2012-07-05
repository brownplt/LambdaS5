function assert(cond) {
  if (!cond) { throw "assert failed"; }
}


function fact(n) {
  var result = 1;
  for (var i = 1; i <= n; i++) {
    result *= i;
  }
  return result;
}

var x = NEWSYM;

assert(typeof x === "number")
assert(x >= 1);
assert(x <= 4);

fact(x);
