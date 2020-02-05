We thank the reviewers for their thoughtful comments.
We will take their comments into account and revise our article as
follows.
* Provide a more detailed comparison with the state of the art
* Discuss the limits of our system

# Inference

Reviewer A argues that inference is not such an important property and
would forbid other interesting features, notably for programming in the large.
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

## Limitations and comparison with Rust

Rust is an established industrial language which evolved over more
than 10 years. Affe highlights a useful accessible point in the design
space, it does not claim to address all of Rust's use cases.

Nevertheless, several features of Rust mentioned by reviewer C
can be adapted to our system, sometimes by just modifying the
"constraint generation" part of Affe.  
The constraint language and its solver are unchanged, which is
a key strength of the constraint-based approach to typing.

- Adapting NNL to our system requires inferring regions
  that are not lexical scopes. Mostly, this wouldn't affect our typing
  rules, but the region inference to obtain
  piecewise lexical scopes.
  We aim to leverage the work by Weiss et al in this direction.
- In Rust, borrows of borrows are done through ad-hoc polymorphism
  (the Borrow and Defer traits) which inserts as many
  borrows as necessary.
  The Affe core language in the paper has two different operators, but
  a surface language would map them to one overloaded operator,
  without compromising any of our results. It also fits with the
  framework of constrained types, but our presentation aims at
  avoiding unnecessary complexity.
- Affe does not require successive borrows, as region
  inference simply places appropriate regions around each of them.
- reviewer D mentions pointers into enums. This concept does not exist
  in ML; only explicit reference types are mutable.

# Functional idioms and combinators

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
