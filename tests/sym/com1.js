var obj = { x : 0 };

function f(unk) {
  unk.x = 1;
  return unk;
}

function g(unk) {
  unk.x = 2;
  return unk;
}

var s = NEWSYM;

COMPARE_RESULTS(
  function () { return f(g(s)); },
  function () { return g(f(s)); },
  function () { return obj.x; }
);
