var i = 0;
var j = 0;
function f(i) {
  j += i;
  return i;
}

j += f(1);
if(j === 2) { print("passed"); }
