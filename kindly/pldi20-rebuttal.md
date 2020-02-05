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
Nevertheless, several 
reasons leads us to consider complete inference as essential:

- Even if a language does not admit full type inference, we believe
  there should be a well-defined core language which does.
  This way, a programmer who steps over the boundary and use these features
  knows when type annotations are needed. 
  In particular, it is possible (and desirable) to extend Affe with
  existential types by requiring type annotations, similarly to Alms.
  The results we present nevertheless garantee that
  full type inference is supported in the absence of existentials.
  This is similar to the current state of OCaml.

- Contrary to what Reviewer A states, ad-hoc polymorphism (type
  classes, traits, implicits, ...) supports complete inference, and such
  extension of Affe would be highly desirable.
  Affe is also designed to work in tandem with a rich, ML-like module
  system, which has been shown support programming in the large very well.

- Linear types and ownerships are known for being fairly heavy to use.
  Rust is no exception and complex elision rules
  for lifetimes were instrumental in increasing ease-of-use. Affe shows
  that we can go much further thanks to inference. This could be used
  to improve ease-of-use of systems which, like rust, only support
  partial inference.

# Related works

As reviewer C points out, the related works is very rich. Due to
limited space, we only gave a small comparison to each relevant work.

## Linear Haskell
LH indeed does have a formalized core calculus. However, only type checking is
formalized, not inference. The inference implemented is
partial (as pointed out by the GHC maintainers themselves), which
is precisely one of the contentious point to consider inclusion in
GHC.
Not only is our inference algorithm formalized, but we
prove its correctness and completeness.

## Limitations and comparison with Rust

Rust is an established industrial language with more than 10 years of
improvements. Affe does not aim to match its range in term of
use-cases, it simply aims to provide a more accessible point in the
design-space.

Nevertheless, several features of Rust pointed by reviewer C
can be adapted to our system. In many cases, we believe these features
can be added by only modifying the "constraint generation" part of Affe. 
The constraint language and its solver are unchanged, which is
precisely the strengths of the typing-by-constraints approach which we use.

- Adapting NNL to our system would requires inferring regions
  that are not lexical scopes. In many cases, this does not require
  changing our typing rules, only our region inference to obtain
  piecewise lexical scopes.
  We aim to leverage the work by Weiss et Al in this direction.
- In rust, borrows of borrows are done through ad-hoc polymorphism
  (the Borrow and Defer traits) which inserts as many
  borrows as necessary.
  The exact same solution works perfectly in Affe: it does not
  compromise inference, works well in a functional setting and
  integrates in our theoretical framework thanks to qualified types.
- Affe does not need to support successive borrows, as our region
  inference will simply place appropriate region around each of them.


# Functional idioms and combinators

Affe supports currying. More generally, any valid core-ML code is valid in
Affe and the inferred type will be more general. This is immediate by
our use of HM(X). Typical functional combinators can all be written,
but their types might not allow manipulating
linear resources or borrows. 
In general, Affe will support borrowing patterns that are not
flow-sensitive. For instance combinators that always borrow each
element, such as our fold, can be written. 
Combinators that might or might not borrow,
depending on their argument (for instance, using permission witnesses)
requires a richer logic (such as mezzo).
