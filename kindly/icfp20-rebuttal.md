We thank the reviewers for their thoughtful comments.
We will take their comments into account and revise our article as follows.
- Expand and improve our examples
- Provide a comparison table with other systems 
- Further discuss limitations of our system

# Reviewer A

> The use of "absolute" natural numbers to identify regions seems not modular.

Affe requires that each region is identified by an index drawn from a partial
order that is compatible with the nesting of regions.
This order can be implemented in many ways, including region variables
as often used in algebraic effects systems, existentials, etc.

For simplicity, the formalization uses the concrete implementation with 
natural numbers for indices. Our proofs only rely on
the partial order and could be adapted to one of the
more abstract approaches.

We plan to add this point to section 6.

> It is very hard to get a grasp what kind of programming idioms can be type checked using Affe.

Affe can easily express rich data-structures (notably 
persistent ones) or manipulate resources and protocols (for instance with session types).

The main limitation of Affe is that it is not flow sensitive.
Code idioms that rely on subtle flow-sensitive usage of 
permissions and linearity do not typecheck in Affe. Such patterns often
do not work in Rust either and require a richer logic as in Mezzo.
As a simple example, Affe can not directly type functions such as the 
merge on linear lists:
```
let rec merge l1 l2 = match l1, l2 with
  | h1::t1, h2::t2 ->
    if &h1 < &h2 
    then h1::(merge t1 l2) (* Must expand l2 to h2::t2 here *)
    else h2::(merge l1 t2)
  | ....
```

Rust slightly relaxes these constraints through the use of non-lexical lifetimes
and double-borrows. 
Following the work by Weiss et al. [38] on the Rust semantics, we believe
these techniques can also be applied to Affe and 
sketch how in section 6, which would help for the example above.

> What is the reason the borrow is fixed to `U` in the splitting rules `SuspB` and `SuspS` (page 10).

For SuspB it should be ok to relax the `U` to `b`. For SuspS, the idea
is that an exclusive borrow is affine. It would most likely be fine in
the present system, but it wouldn't scale to a concurrent setting.
We will check the proofs, implement the most general setting in the
rule, and comment on possible restrictions in a concurrent setting.

> Is Affe's kind mechanism also powerful enough to keep track of things like `Send` and `Sync`?

This is probably better implemented via ad-hoc polymorphism. It is very
desirable to extend Affe with some form of typeclasses, as we point out in
Section 6.2, which would allow to implement such mechanisms.

# Reviewer B

> What could go wrong, for example, if the set function of the array module would use a non-exclusive borrow type in the argument?

The real question here is: "What guarantee is offered by an API?".
ML references and arrays permit concurrent writes but are prone to
data races, which give rise to subtle bugs.

One can prevent such issues dynamically with mutexes, whereas exclusive borrows
forbid concurrent mutations *statically*. The choice then falls on the 
API designer: a file handle is probably better checked statically.
A distributed queue on the other hand would 
feature a `push` function taking a shared borrow precisely
to permit concurrent writes.

While a full description of a concurrent story for Affe is out of scope 
of this paper, such concepts have been used with huge success in the Rust
community to write safe and fast concurrent programs.

# Reviewer C

> in other systems, one might use existential quantification tricks or magic wands to express temporarily borrowing an *element* of an array before returning the element to the array. What would be the equivalent here? 

Indeed, this is something that we would like to add to the system. 
Such functions can already be implemented via closures, 
as demonstrated in the iteration examples in section 2.3:

    val get_borrow :
      ('b <= linₖ) => &('a t) * int * (&(linₖ₊₁, 'a) -{linₖ₊₁}> 'b) -> 'b

This API is however a bit inconvenient. We can improve it using
so called "existential tricks" to match on borrows:

    let &x = get_borrow (a,3) in (* &x must not escape here *)

In general, existential types are not incompatible with Affe and are in fact
one of the first way to extend its expressivity. They also happen to be already implemented in several ML-family languages (OCaml, notably).

> Do you envision a similar discipline for your system where one might write, say, a doubly-linked list in regular GC'd ML, then assume an interface for it that exposes it as a resource?

This pattern is indeed essential and is well demonstrated by Alms.
Affe supports such patterns via subkinding and module type abstraction:
a type can be defined as unrestricted and exposed as linear.

Integrating "forced freeing" of such objects with the GC is more delicate,
and we hope to reuse the work by Munch-Maccagnoni [21] for this purpose.
