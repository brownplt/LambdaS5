# Visualizing Symbolic Execution Traces

Since symbolic execution explores all paths through a program,
the results of symbolically executing a program have an inherent tree 
structure. Each point at which the execution branches defines a node 
of the tree (that's why we call it "branching"), and the results 
define the leaves. We call this tree a trace.

Our evaluator initially just returned a list of values and their 
associated path constraints. In order to reconstruct the trace, we 
needed to accumulate some more information during evaluation.

One approach would have been to restructure the evaluator to construct 
and return the entire tree. However, this would be an invasive change 
and prone to error.

Instead, we chose to simply accumulate a linear trace for each 
result---a list of the branch points encountered on the path to the 
result, along with a record of the decision made at each branch point. 
After accumulating a linear trace for each result, we were able to 
merge all of the linear traces together to create the tree trace with 
a simple structurally recursive algorithm.

One potential issue with this strategy is that the branch points are 
not unique. For instance, a recursive procedure application or a 
simple loop might repeatedly lead to the same branch point. However, 
the *sequence* of branch points encountered will be unique for each 
path through the program, so we are safe. From this perspective, 
constructing the tree trace from the linear traces is much like 
constructing a prefix tree from a set of strings.

We then tried outputting these tree traces with regular printing, but 
the trees were so large that the format quickly became unreadable. 
Instead, we decided to print out the traces in DOT format (a format 
for describing graphs) and then visualize them using Graphviz.
