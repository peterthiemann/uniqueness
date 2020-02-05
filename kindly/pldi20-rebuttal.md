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
Nevertheless, several 
reasons leads us to consider complete inference as essential:

- Even if a language does not admit full type inference, we believe
  there should be a well-defined core language which does.
  This way, a programmer who steps over the boundary and use these features
  knows when type annotations are needed. 
  In particular, it is possible (and desirable) to extend Affe with
  existential types by requiring type annotations, similarly to Alms.
  The results we present nevertheless guarantee that
  full type inference is supported in the absence of existentials.
  This is similar to the current state of OCaml.

- Contrary to what Reviewer A states, ad-hoc polymorphism (type
  classes, traits, implicits, ...) supports complete inference, and such
  extension of Affe would be highly desirable.
  Affe is also designed to work in tandem with a rich, ML-like module
  system, which has been shown to support programming in the large very well.

- Linear types and ownership are known for being fairly heavy to use.
  Rust is no exception and complex elision rules
  for lifetimes were instrumental in increasing ease-of-use. Affe shows
  that we can go much further thanks to inference. This could be used
  to improve ease-of-use of systems which, like Rust, only support
  partial inference.

# Related works

As several reviewers point out, the related works is very rich. Due to
limited space, we only gave a small comparison to each relevant work.
We will expand our article in this direction and
now answer specific questions.

## Linear Haskell
LH does indeed have a formalized core calculus. 
However, only type checking is formalized, not inference. 
The inference implemented is
partial (as pointed out by the GHC maintainers themselves), which
is precisely one of the contentious point for inclusion in GHC.
Not only is our inference algorithm formalized, but we
prove its correctness and completeness.

## Rust
Rust is an established industrial language with more than 10 years of
improvements. Affe does not (yet!) aim to match its range in term of
use-cases, it simply provides a more accessible point in the
design-space.

Nevertheless, several features of Rust pointed by reviewer D
can be adapted to our system. In many cases, we believe these features
can be added by only modifying the "constraint generation" part of Affe. 
The constraint language and its solver would be unchanged, which is
precisely the strengths of the typing-by-constraints approach we use.

- Adapting Non-lexical lifetimes (NNL) to our system would require 
  inferring regions that are not lexical scopes. 
  Concretely, this means that a region is a cover tree of the
  control flow graph, instead of the graph of all paths between two points.
  Inferring such precise regions is very desirable, and we believe
  it can be done by improving our region inference, without affecting the
  rest of the system.
- In rust, borrows of borrows are often done through ad-hoc polymorphism
  (the Borrow and Defer traits) which inserts as many
  borrows as necessary.
  The exact same solution works perfectly in Affe: it does not
  compromise inference, works well in a functional setting and
  integrates in our theoretical framework thanks to qualified types.
- Affe does not need to support successive borrows (i.e., borrows in
  successive expressions) as region
  inference will place appropriate regions around each of them.
- The extension to algebraic data types is easy and done in our
  prototype. The only difficulty is to verify nesting: notably
  linear objects must not live inside unrestricted types.
- Interior mutability is the ability to mutate an object from a shared
  borrow. In rust, this is provided by an unsafe primitive.
  Affe would generally have the same constraints. However, Affe can safely
  express types such as Cell using mutable records:
  
  type ('a : 'k) ref : 'k = { mutable content : 'a } where ('k <= un)

  
# Functional idioms and combinators

Reviewer C wonders about Affe's support for functional combinators and idioms.
Affe supports currying. More generally, any valid core-ML code is valid in
Affe and the inferred type will be more general. This is immediate by
our use of HM(X). Typical functional combinators can all be written,
but their types might not allow manipulating
linear resources or borrows. 
Affe also supports borrowing patterns that are not
flow-sensitive. For instance combinators that always borrow each
element, such as our fold, can be written. 

# Limitations

Reviewer C and D asks to details the limitations of our system.
Most limitations are due to the fact that Affe's type algebra
is voluntarily simple:

- Affe is not flow-sensitive, and will not be able to express
functions that might or might use something depending on their
argument. More generally, we don't support borrowing pattern
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
