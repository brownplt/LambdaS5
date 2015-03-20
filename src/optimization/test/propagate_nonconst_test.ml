




(* in this case, only f should be propagated *)
(cmp
   "let (x=1)
      let (f = func() {x})
      let (g = func() {f()})
      let (x=2)
        g()"
     "let (x=1)
      let (f = func() {x})
      let (g = func() {(func(){x})()})
      let (x=2)
        g()");

(* in this case, g can be propagated as well *)
(cmp
   "let (x=1)
      let (f = func() {x})
      let (g = func() {f()})
      let (x=2)
        g()"
     "let (x=1)
      let (f = func() {x})
      let (g = func() {(func(){x})()})
      let (t=2)
        func(){(func(){x})}()");

(* t's free variable is at the formal args: renaming func *)
(cmp
  "let (x = 1)
   let (y = 2)
   let (t = func(){prim('+',x,y)})
   func(x) {
      x := t
   }"
  "let (x = 1)
   let (y = 2)
   let (t = func(){prim('+',x,y)})
   func(x1) {
      x1 := func(){prim('+',x,y)}
   }");

(* let bind shadows the formal argument again *)
(cmp
  "let (x = 1)
   let (y = 2)
   let (t = func(){prim('+',x,y)})
   func(x) {
      let (x = 2)
         t();
      x
   }"
  "let (x = 1)
   let (y = 2)
   let (t = func(){prim('+',x,y)})
   func(x1) {
     let (x2 = 2)
       func(){pim('+',x,y)}();
     x1
   }");

(cmp
  "let (x = 1)
   let (y = 2)
   let (t = func(){prim('+',x,y)})
   func(x) {
      let (y = 2)
         t();
      x
   }"
  "let (x = 1)
   let (y = 2)
   let (t = func(){prim('+',x,y)})
   func(x1) {
     let (y1 = 2)
       func(){pim('+',x,y)}();
     x1
   }")
