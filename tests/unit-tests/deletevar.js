function foo() {
   var x = 3;
   delete x;
   if (x === 3) {
      print("passed");
   }
}

foo();
