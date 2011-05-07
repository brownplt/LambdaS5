var o = {"a" : 0, "b" : 1};
var count = 0;

for (var x in o) {
   print(x);
   count = count + 1;
}

if (count === 2) {
   print("passed");
}
