We thank the reviewers for their thoughtful comments.
We will take their comments into account and revise our article as
follows.
* Provide a more detailed comparison with the state of the art
* Discuss the limits of our system

# Inference

Reviewer A argues that inference is not such an important property and
would preclude other interesting features, notably for programming in the large.
This is partially a cultural question: Haskell and Rust users are used
to annotations while ML programmers are not.
We consider type inference as essential for several reaons:

- Type annotations complement and empower type inference.
  Our proposal gives a well-defined core language with full type
  inference. In an extended language, type annotations will be
  required where a programmer uses the extensions, but the rest will
  be inferred.
  For example, it is possible (and desirable) to extend Affe with
  existential types (as in Alms), which requires type annotations, but
  *only* in places that deal with existentials.
  This is similar to the current state of OCaml.

- Contrary to what Reviewer A states, ad-hoc polymorphism (type
  classes, traits, implicits, ...) supports complete inference, and such
  extension of Affe would be highly desirable.
  Affe is designed to work with an ML-like module
  system, which is proven to support programming in the large.

- Linear types and ownership are notoriously tricky concepts.
  Rust is no exception and complex elision rules
  for lifetimes were instrumental in increasing ease-of-use. Affe shows
  that we can go much further thanks to inference. This could be used
  to improve ease-of-use of systems which, like Rust, only support
  partial inference.

# Related work (Reviewer C)

Due to limited space, we can only compare with a selection of the most
relevant work. We will incude more if there is more space in the final paper.

## Linear Haskell

LH comes with the metatheory culminating in type soundness. However,
*type inference* for LH is not formalized and only sketched in the
paper. (This is particularly concerning in the light of two POPL2020
papers that highlight subtle issues in typechecking Haskell.)
In contrast, our inference algorithm is formalized and we
prove its correctness and completeness.

## Rust

Rust is an established industrial language which evolved over more
than 10 years. Affe highlights an important point in the design
space, it does not claim to address all of Rust's use cases.

Nevertheless, several features of Rust mentioned by reviewer D
can be adapted to our system, sometimes by just modifying the
"constraint generation" part of Affe.  
The constraint language and its solver remain the same, which is
a key strength of the constraint-based approach to typing.

- Adapting NNL to our system requires inferring regions
  that are not lexical scopes. 
  Concretely, a region is a cover tree of the
  control flow graph, instead of the graph of all paths between two points.
  Inferring such precise regions is very desirable, and we believe
  it can be done by improving our region inference, without affecting the
  rest of the system.
- In Rust, borrows of borrows are done through ad-hoc polymorphism
  (the Borrow and Defer traits) which inserts as many
  borrows as necessary.
  The Affe core language in the paper has two different operators, but
  a surface language would map them to one overloaded operator,
  without compromising any of our results. It also fits with the
  framework of constrained types, but our presentation aims at
  avoiding unnecessary complexity.
- Affe does not require successive borrows, as region
  inference places appropriate regions around each of them.
- The extension to algebraic data types is easy and done in our
  prototype. The only difficulty is to verify nesting: 
  linear objects must not live inside unrestricted types.
- Interior mutability is the ability to mutate an object from a shared
  borrow. This is an usafe primitive In Rust.
  Affe would have similar constraints. However, Affe can safely
  express types such as Cell using mutable records:
  
  type ('a : 'k) ref : 'k = { mutable content : 'a } where ('k <= un)
  
# Functional idioms and combinators (reviewer C)

Affe supports currying as it is a strict superset of core-ML. The
additional constraints only affect linearity.

In particular, all familiar combinators are typable with their familiar
ML type; their principal linearity constraints will indicate whether
the combinator is compatible with linear resources and/or borrows.

In general, Affe supports borrowing patterns that are not
flow-sensitive. For instance, combinators that always borrow each
element, such as our fold, can be written. 
A function that may or may not borrow,
depending on an argument (for instance, using permission witnesses)
requires a richer logic (such as Mezzo).

# Limitations

Reviewer C and D asks to detail the limitations of our system.
Most limitations are due to the fact that Affe's type algebra
is voluntarily simple:

- Affe is not flow-sensitive, and will not be able to express
functions that might or might not use something depending on their
argument. More generally, we don't support borrowing patterns
whose correctness depends on internal invariants of a data-structure.
This requires richer logic such as Mezzo, typestates, etc.
As a simple example, Affe can not directly type functions such as the 
merge on linear lists:

  let rec merge l1 l2 = match l1, l2 with
    | h1::t1, h2::t2 ->
      if &h1 < &h2 
      then h1::(merge t1 l2) (* Must expand l2 to h2::t2 here *)
      else h2::(merge l1 t2)
    | ....

- In Rust, many primitives are written using unsafe code which is
  then abstracted. Such unsafe code can be then proven correct (see
  RustBelt).
  Affe aims to use module abstraction similarly, but is much
  more limited and doesn't provide such a language-integrate
  unsafe mechanism.

- Affe's semantics is similar to ML: pass by reference and GC.
  Many linear languages, and Rust in particular, support very precise
  control over memory structures and call conventions which we do not
  aim to provide.

# Please explain in author response (reviewer D):

## how to read
    "let*? () = rho ? b && rho \in pi ..."

This is explained in the text. "let*? () = bool-expression" evaluates
the boolean expression and reduces to "return ()" when true and fails
otherwise.

## stack of modifiers

Each borrow adds its kind to the address. The addition checks whether
the new borrow is permissible (the "rho ? b" operator): we cannot take
a mutable borrow of an immutable borrow. This happens on entry to the
borrow's region. The soundness proof maintains the currently
accessible borrows in the set of permissions, which is also managed by
the operational semantics (however, all of this manipulation can be
elided in an impementation; the instrumented semantics is only needed
for the soundness proof).
