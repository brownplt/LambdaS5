# (Not) Symbolically Executing Symbolic Functions

When trying to symbolically execute a language like JavaScript, which 
has both first-class functions and mutation, a big problem arises. If 
you allow symbolic values to be any type of JavaScript value, then it 
is possible for a symbolic value to be a function. A symbolic function 
could have any code inside of it and could close over any environment, 
which means that applying it could have unknown effects on the heap.

There's a few different strategies for handling symbolic functions:

1. When we try to apply a symbolic function, don't execute that 
   branch, but instead emit some sort of warning message. 

2. When we try to apply a symbolic function, assume it's pure, and 
   return a new symbolic value (our current strategy).

3. Have the user give some sort of annotations to describe the 
   symbolic function. For instance, we could support an annotation
   to say if a symbolic function is pure w/r/t its external context, 
   or annotations describing the pieces of external state that might 
   be mutated by the function.

These strategies might not be mutually exclusive. We could default to 1.
or 2. but also integrate any additional information from annotations.
