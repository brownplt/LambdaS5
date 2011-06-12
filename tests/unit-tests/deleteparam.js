function f1(a) {
   delete a;
   return a;
}

if (!(f1(1) !== 1)) {
   print("passed");
}
