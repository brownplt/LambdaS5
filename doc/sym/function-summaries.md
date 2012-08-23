# Symbolic Function Summaries

## The Basics

In order to avoid symbolically executing the same bits of code over
and over, we want to symbolically execute a function once, make a
summary of its results (which input conditions lead to which outputs),
and then, whenever we call that function, instead of executing it,
just use the results from the summary. For each possible result in the
summary, we use it if the arguments with which the function is called
satisfy its input conditions.

## Related Work

The idea as described above has been used to implement "compositional 
symbolic execution," which consists of symbolic executing some chunk 
of code, summarizing the result, and then combining it with either 
concrete executions or other summarized chunks in various ways.

Some examples:

<http://dl.acm.org/citation.cfm?id=1453131>

<https://lirias.kuleuven.be/bitstream/123456789/291808/1/main.pdf>

<http://wiki.epfl.ch/edicpublic/documents/Candidacy%20exam/bucur_proposal.pdf>

## The Problems

Generating and checking input conditions is simple if your constraint
language covers all possible values manipulated by your program. Since
symbolically executing a function with unknown inputs by definition
creates a set of constraints on those inputs, the summary is just the
pair (return value, constraints) for each possible branch.

However, if you can't represent all values in the constraint language,
then things get more complicated. For us, the problem has to do with
objects, both in the way they are referenced as symbolic values and in
the way they are represented in the evaluator.

For instance, when summarizing the function `ToNumber(x)`, which
performs a different conversion based on the type of `x`, we first
branch on whether or not `x`, which is initially a new symbolic value
of unknown type, is a pointer to an object. If `x` is a pointer, we
consider branches where `x` is pointing to any of the concrete objects
on the heap, or a new symbolic object.

When we want to apply the summary, in some of these branches we should
have an assertion that the argument `x` must be an object. However,
since we concretized `x` to be a pointer to an object, it is no longer
a symbolic value, so we can't generate constraints on it.

One solution to this might be to add a symbolic value corresponding to
the object, and generate constraints on that value while actually
still evaluating with the concrete object. However, if we figure out a
good (i.e. sound and efficient) way to do this, we might as well be
using just the symbolic value representation for the object in
general. The difficulies associated with doing that were the reason we
chose to represent objects explicitly in the first place.

A second issue with objects arises when a summarized function performs
read and write operations on them, because these result in symbolic
side-effects. Reading from a symbolic object results in a property
possibly being added to the object (if it wasn't found). Again, if we
could talk about objects in the constraint language, it would be easy
to encode these types of conditions, but since we can't, all we can
look at is the resulting store after finishing the generation of the
summary.

We might take this resulting store and compare it to the initial store
(from before starting the generation of the summary), counting any
differences as input conditions. However, there's no way to know which
differences came from these symbolic side-effects (which would be
input conditions) and which came from concrete side-effects (which
would be *output* conditions---i.e. the result of applying the
summary, not constraints on the arguments).

## Solving the Problems

One way to possibly solve these problems would be to create a new
constraint language for summaries that would be a superset of the
language used for the path constraint. The new language would need to
be able to encode constraints on pointers (e.g. symbolic value `x` is
a pointer to object `o`) as well as constraints on object fields (e.g.
symbolic object `o` has value `v` at field `f`).

There would also have to be some mechanism for creating these
constraints. Given the nature of the problems, it seems like it would
be too difficult to continue to try to use the evaluator as a black
box for creating summaries. When trying to generate constraints based
on the results of the evaluation, too much information has already
been lost. Thus, the evaluator would need to be modified to accumulate
the appropriate constraints using the new language, while still using
the old constraint language to talk to the SMT solver.
