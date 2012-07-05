function assert(cond) {
  if (!cond) { throw "assert failed"; }
}

function fact(n) {
  function helper(n, acc) {
    //assert(n >= 1);
    return (n === 1)
      ? acc
      : helper(n - 1, n * acc);
  }
  return helper(n, 1);
}

var x = NEWSYM;

assert(typeof x === "number")
assert(x >= 1);
assert(x <= 6);

fact(x);
