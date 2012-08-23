# Symbolic Execution with Dynamic Typing

## Related Work

Currently, no one has attempted to apply symbolic execution to a
dynamically typed language in a manner that allows symbolic inputs to
be of unknown type. There have been a few systems that use symbolic
execution to analyze a dynamically typed language, but they appear to
restrict the types of the symbolic inputs.

### Kudzu
<http://webblaze.cs.berkeley.edu/2010/kudzu/kudzu.pdf>

Symbolically executes JavaScript, allowing strings, integers, or
booleans as symbolic inputs. However, it appears that these inputs
have prespecified types. Any type conversions are then handled by
their satisfiability solver. It seems that they built the solver to
mostly focus on string inputs. In any case, they don't allow for
symbolic objects.


### Rozzle
<http://research.microsoft.com/en-us/um/people/livshits/papers/tr/rozzle_tr.pdf>

Does "multi-execution" of JavaScript, which isn't like regular
symbolic execution. Instead of exploring multiple execution paths,
their representation of a symbolic value is a tree representing
different possible concrete values. They only execute a program once,
but embed the branching possibilities in the values. These symbolic
values have a type annotation.

### Mix
<http://www.cs.umd.edu/~jfoster/papers/cs-tr-4954.pdf>

A system that mixes type checking and symbolic execution. The idea
is to perform type checking on some blocks of code and symbolic
execution on others (using whichever technique is more appropriate).
The prototype analyzes C. Their symbolic values have type annotations,
which they use to ensure that operations on symbolic operands are well
typed. The only bit of allowance for uknown types that they discuss is
whether a pointer will be null or not (sect 4.1). Otherwise, it seems
that their analysis is at a low enough level that they don't need to
worry about unknown types.

### Apollo
<http://www.cs.washington.edu/homes/mernst/pubs/bugs-webapps-tse2010.pdf>

Combines concrete and symbolic execution to analyze PHP, restricting
symbolic inputs to strings and integers.


## Our Approach

We apply symbolic execution to JavaScript, but do not restrict the
possible types of symbolic inputs.^[Not entirely true---we don't allow
them to be functions at the moment.]

One easy way to handle this would be to symbolically execute a program
given every possible combination of types for the symbolic inputs.
However, since the execution will be identical up to the point that
the symbolic inputs are actually used in the program, this can result
in unnecessary repeated work. Furthermore, we can do better with
regard to efficiency than explicitly trying every combination.

Instead, for every symbolic value $x$, we associate with it another
symbolic value $\tau_x$, the type of $x$. Whereas $x$ may be any value
in the JavaScript value space, $\tau_x$ can be any one of the set of
JavaScript types: { String, Number, Boolean, Undefined, Null,
ObjectPointer }. As we symbolically execute code involving $x$, we
accumulate constraints on $\tau_x$.

For example, consider the following code:

~~~ { .javascript .numberLines }
function safeDivide(y, x) {
  if (x === 0) {
    throw "Tried to divide by 0!";
  } else {
    return y / x;
  }
}
~~~

If we execute this function one symbolic argument (e.g. `safeDivide(5,
x)`, where `x` holds symbolic value $x$), then when we hit the
condition on line 2, we have two possible branches, one where
$x = 0 \wedge \tau_x =$ Number, and a second where
$x \neq 0 \vee \tau_x \neq$ Number. The important thing to notice is
that since we don't know the type of $x$, the `===` operator not only
creates constraints on the values, but also on the types of those
values.

The JavaScript primitive operator `/` expects two Numbers. If give
operands of other types, it tries to convert these values into
Numbers. Otherwise it returns `NaN`. Thus, in the second branch, when
we try to perform the division, we have multiple possiblities based on
the possible values for $\tau_x$.

If $\tau_x =$ Number, then $x \neq 0$, so we can return the result of
the division as a new symbolic value $z$, where $z = x / 5$.

If $\tau_x \neq$ Number, then we have to explore every other possible
type. Some of these will lead to `NaN`, but there are some more
interesting cases. If $\tau_x =$ Boolean, and $x =$ `true`, then the
result will be 5, because `true` will be converted to its Number
equivalent, 1 (can you guess what happens with `false`?). If $\tau_x =$
String, and $x =$ `"0"`, then the result is `Infinity`, as the String is
converted into its Number equivalent.

Thus, by performing symbolic execution using a symbolic value of
unknown type, we learn that our function is actually not safe at all,
and can still lead to division by 0 or a host of other unexpected
behaviors.^[These are the actual results we get from the symbolic
evaluator!]

We might try to make our function safer by adding in a check to make sure
the two arguments have the same type, like so:

~~~ { .javascript .numberLines }
function safeDivide2(y, x) {
  if (x === 0) {
    throw "Tried to divide by 0!";
  } else {
    if (typeof x === typeof y) {
      return y / x;
    }
  }
}
~~~

We can learn even more (and also demonstrate the strength of our
approach to unknown types) by executing the improved version of the
function with two symbolic values: `safeDivide2(y, x)`, where `y` holds
symbolic value $y$ with type $\tau_y$ and `x` holds symbolic value $x$
with type $\tau_x$.

When we execute the `else` branch, we know that $x \neq 0 \vee \tau_x
\neq$ Number, just like in the old version. When we branch for the
condition on line 5, on the true branch, we add the constraint that
$\tau_x = \tau_y$. So now in the case that we execute the division,
our full path constraint is $(x \neq 0 \vee \tau_x \neq$ Number
$)\wedge \tau_x = \tau_y$. When we branch on the multiple
possibilities for $\tau_x$, the only feasible branches will be the
ones where $\tau_x = \tau_y$.

Of course, this function is still not entirely safe, but it serves to
demonstrate how type information about symbolic values can be
propogated through constraints. One can imagine a situation where the
types of multiple symbolic values might be bound together by a network
of constraints.
