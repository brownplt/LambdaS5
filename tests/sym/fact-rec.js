function assert(cond) {
  if (!cond) { throw "assert failed"; }
}

function fact(n) {
  assert(n >= 1);
  return n === 1 ? 1 : n * fact(n-1);
}

var x = NEWSYM;

assert(typeof x === "number")
assert(x >= 1);
assert(x <= 4);

fact(x);
