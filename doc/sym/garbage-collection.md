# Symbolic Execution with Garbage Collection

## Related Work

As far as we know, nobody has explored novel garbage collection 
techniques for use with symbolic execution.

## Our Approach

**Note:** Our strategy is tied to the way we represent objects. Make 
sure you read about that first.

To perform garbage collection in the symbolic evaluator, we just need 
to make a few modifications to a standard algorithm. In our case, we 
used the mark-and-sweep algorithm, where all values reachable from the 
root set (the set of values bound in the environment) are first 
marked, and then any unmarked values are garbage collected, or swept.

Normally, a value is reachable if there is a chain of references that 
lead from a member of the root set to the value. Since we introduce 
new kinds of values in symbolic execution, we have to modify our 
notion of reachability.

Since unitialized symbolic values might end up being pointers to 
objects, they need to know all of the possible locations they can 
point to. The same is true for symbolic objects, since they might need 
to create new symbolic values to return when a property is accessed.
We consider the list of locations stored by these two types of values 
as references, since the objects they point to might be needed later 
on.

We perform garbage collection before creating any new symbolic value, 
so that its list of locations will be minimal. This helps reduce the 
number of paths created when branching in the case that a new symbolic
value is a pointer to an object.
