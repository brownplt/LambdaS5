# Symbolic Execution with JavaScript Objects

JavaScript objects are a bit odd when it comes to symbolic execution.
They are fundamentally just mappings from keys (strings in this case)
to values, to which new keys can be added at any time. In this sense,
they are like arrays or hashes, for which there exists a fairly
standard approach when it comes to symbolic execution, developed for
symbolic execution of languages such as Ruby.

However, since the objects themselves are referenced by pointers, and
can recursively point to other objects, some sort of symbolic alias
analysis is also required. This issue has also been tackled in
symbolic execution of languages like Java.

Due to the absence of type information and prototype-based
inheritance, symbolic execution with JavaScript objects requires both
a combination of these previous strategies as well as some novel
approaches.

## Related Work

### Rubyx

<http://www.cs.umd.edu/~jfoster/papers/ccs10.pdf>

Symbolically executes Ruby code. Since the fields of a Ruby object are
all defined at compile time, a symbolic object in this case is just an
instance of the object where the values of the fields are unknown.
Thus, Rubyx does not deal with issues of symbolic pointers. More
relevant is the way that Rubyx models arrays and hashes. Arrays (and
hashes) are modeled with constraints given to their STP solver, Yices,
using uninterpreted functions subject to the standard array axioms.
It's unclear exactly how (or if) nested arrays were modeled, since
Yices does not support recursive datatypes.

### Kiasan

<http://www.sireum.org>

<http://people.cis.ksu.edu/~robby/SAnToS-TR2009-09-25.pdf>

<http://people.cis.ksu.edu/~hatcliff/Papers/Deng-al--SEFM07-TR>

Symbolically executes Java code using the lazy/lazier/lazier\#
initialization algorithms to handle object pointer aliasing. The basic
idea of these algorithms is to be as lazy as possible when
initializing unknown values that are accessed from fields , since it
is not always necessary to initialize the value completely (which
often involves creating many new execution paths). For instance, if a
value is being accessed just to check whether it is non-null, it is
not necessary to perform any alias analysis.

## Our Approach

### Object Values

To model JavaScript objects, we use a slightly different approach than
Rubyx. Since STP solvers generally do not support the kinds of
recursive datatypes necessary to model nested objects, we implement
support for objects within the evaluator.

We choose the naive representation for objects: a map (in the language
of our evaluator---OCaml) from string keys to JavaScript values. To
handle symbolic fields, we augment this map with a second map from
symbolic string keys to JavaScript values. The invariant on the fields
in these two maps is that each field name is not equal to any other
field name in either of the two maps.^[This is trivially true for
fields in the same map.] (When we say "equal," we mean equal in the 
eyes of the SMT solver.)

Reading and writing fields thus consists of as maintaining this
invariant while exploring all possible branches. For example, if `obj`
is an object and `f` is a symbolic string, the lookup expression
`obj[f]` produces branches for each case where `f` is equal to one of
the field names in the concrete or symbolic field map, as well as one
branch where it is not equal to any of them.

The full algorithm (omitting all the annoying edge cases caused by 
JavaScript object and property attributes) looks like this:

Let `f` be the field, `obj` be the object, `prop(x)` be the prop at 
field `x`

1. If `obj` is null, return `None`
2. If `f` is concrete (and a string)
    a. If `f` is in the concrete fields, return `prop(f)`
    b. Otherwise, we branch:
        1. For each `f'` in sym fields, create a branch, assert `f` = `f'`, 
           and return `prop(f')`
        2. Create a branch, assert for all `f'` in sym fields, `f` 
           $\neq$ `f'`, and recurse on the prototype of `obj`
        3. If `obj` symbolic, create a branch, assert for all `f'` in 
           sym fields, `f` $\neq$ `f'`, add a prop `p` containing a 
           new sym val to the con fields of `obj` at `f`, return `p`

3. If `f` is symbolic (and a string)
    a. If `f` is in the symbolic fields, return `prop(f)`
    b. Otherwise, we branch:
        1. For each `f'` in concrete or sym fields, create a branch, 
           assert `f` = `f'`, and return `prop(f')`
        2. Create a branch, assert for all `f'` in concrete or sym 
           fields, `f` $\neq$ `f'`, and recurse on the prototype of `obj`
        3. If `obj` symbolic, create a branch, assert for all `f'` in 
           concrete or sym fields, `f` $\neq$ `f'`, add a prop `p` 
           containing a new sym val to the sym fields of `obj` at `f`, 
           return `p`

Note that the two latter cases are nearly symmetrical, but when `f` is
concrete, we don't need to check the cases where `f` is asserted equal
to some other concrete field, since we know those are going to be 
unsatisfiable.

Writes are performed similarly, inserting instead of looking up. In 
cases 2.b.3 and 3.b.3, we don't need to create a new sym value, we 
just add a new field to the appropriate map.

The advantages to this approach are:

1.  We don't have to hack in a way to represent the recursive 
    definition of the object type to our SMT solver, possibly 
    sacrificing specificity/accuracy. It remains unclear whether Rubyx 
    supports nested arrays and hashes.

2.  When mixing concrete values and symbolic values, the concrete 
    values can still exist in the evaluator, instead of being 
    converted into symbolic values and having to rely solely on the 
    SMT solver. For instance, consider the follwing program:

    ```javascript
    var f = NEWSYM;
    var obj = {};
    obj[f] = 2;
    print( obj[f] );
    ```

    If we were to represent objects solely in the SMT solver, then 
    this program would print out a symbolic value (that the SMT solver 
    could tell us must be equal to 2). With our explicit 
    representation of objects, this program simply prints out 2.

    While the algorithm is more complex than just handing off all 
    object operations to the SMT solver, in return our evaluator gives 
    us more explicit results. For a language like JavaScript, where 
    objects are used for just about anything, it's important to keep 
    things close to concrete. Otherwise, constraints would quickly grow 
    in size and complexity to the point where interpreting them would 
    require, well, an interpreter.

### Pointers to Objects

The second aspect of JavaScript objects that makes them so complex for 
symbolic execution is that variables store pointers to objects, not 
the object literals themselves. That means that a new symbolic value 
can either be a scalar value (number, string, undefined, etc.) or a 
pointer to an object.

Of course, it's not necessary to create branches for these two 
possibilities when a variable is first assigned a symbolic value; 
rather, we can wait until the symbolic value is used in an 
operation that will determine whether it is a scalar or a pointer. 
Thus, we use a value we call a NewSym, which can be either a scalar or 
a pointer.

If we have determined on some branch that a NewSym is a pointer to an 
object, we still don't know which object it points to. We have several 
options in this situation:

1.  Say it points to some symbolic object which we know nothing about.
2.  Create branches in which it points to each of the objects that 
    existed on the heap at the time it was declared, or some symbolic 
    object.

Option 1. subsumes option 2., since the symbolic object could take the 
form of any of the concrete objects on the heap. However, option 2.
will give us more specific information, since it is at least somewhat 
likely that the declaration of the symbolic value stands in the place 
of an assignment to some pre-existing object as opposed to some new 
object literal.

We choose option 3., which is to not choose either option 1. or 2. 
until we actually need to---i.e. until the pointer is used in an 
operation that needs to know about the object it points to. For 
example, if we only want to check that the pointer is a pointer, we 
don't need to know which object it points to. Once we do need the 
actual object, we choose option 2., keeping in line with the principle 
of keeping things concrete and explicit when possible. Thus, we must 
introduce the notion of a symbolic pointer, which holds a list of all 
the possible locations it might point to.

This approach of not making choices until we need to is similar to the 
lazy/lazier/lazier\# initialization algorithms used in Kiasan, which 
can be summarized as follows:

Lazy initialization:
:   Delays the choice of which value is stored in a field of an object 
    until the field is accessed.

Lazier initialization:
:   For a field storing a pointer, delays the choice of which object
    the pointer points to (including in the set of possible objects
    `null`).

Lazier\# initialization:
:   For a field storing a pointer, delays the choice of whether the 
    pointer points to `null` or to an object.

Our representation for objects achieves the same effect as lazy 
initialization, since we not only don't initialize the values stored 
in fields of a symbolic object, but since fields can be added and 
removed dynamically, we do not even initialize the fields.

The lazier and lazier\# algorithms are similar to our approach of 
delaying the choice of initializing a pointer until it is 
dereferenced. However, Kiasan's algorithms only apply to fields of 
symbolic objects, whereas our approach applies to general symbolic 
values. Kiasan executes Java code, and therefore has type information 
about all new symbolic values, whereas we do not have the same luxury.
Thus, when a new symbolic variable is created, we must leave all 
options open, and therefore choose to be as lazy as possible. This is 
discussed in further detail in our approach to types.

We may be able to push this laziness even further by being lazy about 
object and property attributes. Our symbolic pointers delay the choice 
of object. However, sometimes a symbolic pointer is concretized only 
to check whether the object it points to is extensible, an attribute 
which at worst can only divide the set of possible objects pointed to 
into two classes: the extensible objects and the non-extensible 
objects. It may be possible to create symbolic pointers which also 
contain constraints on the attributes of the objects they point to, 
but this will take further investigation.
