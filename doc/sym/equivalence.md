# Using Symbolic Execution to Test Behavioral Equivalence

Since symbolic execution gives us a complete account of the behavior 
of a program in relation to its inputs, we can use it to test whether 
two programs behave equivalently. This has many possible applications, 
including checking the correctness of refactorings and optimizations 
and comparing algorithms.

## Related Work

### Java PathFinder

<http://dl.acm.org/citation.cfm?id=1453131>

Java PathFinder supports differential symbolic execution, a technique 
which consists of computing the diff between two versions of a program 
and then testing the equivalence of changed methods. To test 
equivalence, each version of the method is symbolically executed to 
produce a summary of its behavior, and then the summaries are compared 
with respect to various measures of equivalence (which are outlined in 
detail in the paper). When summarizing methods, they do not perform 
full symbolic execution, instead modeling pieces of code common to 
both versions of a method with uninterpreted functions.

## Our Approach

The non-trivial part of testing for behavioral equivalence is defining 
a useful notion of equivalence. We define two programs to be 
equivalent when for each possible result $r$ of the first program, 
there exists a possible result $r'$ of the second program such that
the constraint $r = r'$ is satisfiable (given the path constraints 
associated with both $r$ and $r'$). Intuitively, this means that two 
programs will be deemed equivalent if they produce the same set of 
outputs.

However, this definition of equivalence is lacking in one respect. For 
example, consider the following versions of a program:

```javascript
function isPositive1(n) {
    return n > 0;
}
```

```javascript
function isPositive2(n) {
    return n >= 0;
}
```

These two functions produce all of the same outputs (`true` and 
`false`), but clearly do not behave equivalently. Or consider this 
more blatant example:

```javascript
function isPositive3(n) {
    return n < 0;
}
```

This function is not even close to behaving the same as the first 
version, but would still be deemed equivalent under our notion of 
equivalence.

When checking equivalence, we need to somehow bind the results to the 
constraints on the input values. Thus, we should define a new notion 
of equivalence: that two programs are equivalent when for each 
possible result $r$ of the first program, there exists a possible 
result $r'$ of the second program such that 1)
the constraint $r = r'$ is satisfiable, and 2) for each input $i$ of 
the first program, for each corresponding input $i'$ of the second 
program, the constraint $i = i'$ is satisfiable (given the path 
constraints associated with both $r$ and $r'$).

With this improved notion of equivalence, two programs will only be 
considered equivalent if they behave the same when given the same 
inputs. 
