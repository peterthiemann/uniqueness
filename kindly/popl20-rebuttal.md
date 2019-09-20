We thanks the reviewers for their thoughtful comments. We will take their comments into account and revise our article in the following manner:
- Streamline the description of examples in Section 2 to focus on Affe's novelties
- Present automatic region annotation in the body of the article and clarify its role in the type system.
- Present the pattern matching rules, both typing and semantic.
- Improve the explanation through new examples for the semantics and the type inference (an example for constraint solving is already present in the appendix).


# Reviewer A

> How is proper nesting of regions enforced, for both the type system and region inference in Appendix A?  And for the example I asked about above ( $\{|\ldots\{|\ldots|\}^2|\}^3$ )? Or does the paper simply give a nesting intuition that's not necessary because the indices don't actually matter for soundness?

We assume that the type checker operates on a program where
region annotations are inserted by the automatic
annotation phase provided in Appendix A.
So our typing rules do not check the nesting because they are supposed
to work only on programs with well-nested regions (a similar situation
occurs in type-based program analysis, where the analysis assumes a
well-typed program and only reasons about additional properties on values).
Unfortunately, the annotation rules have a typo: The recursive
call in "Rewrite-Region" should be on $n+1$.
Insertion of annotations is completely deterministic (which solves principality concerns)
and ensures that indices grow as regions are nested (which rules out all the given
problematic examples).
This is sufficient since there is no way to hide the level of a borrow
and smuggle it past a region boundary. 
If that was the case, for instance with existential types, we would require a
more sophisticated region system with abstract variables, as suggested
by the reviewer.

We agree that our assumption should be made clearer and will improve
the associated explanations.

> Please explain why/whether Theorem F.2's statement properly enforces linearity

We don't understand the construction outlined by the reviewer. We
believe that the situation cannot arise because the
different parts of the environment are always disjoint. The
Region/SRegion rule moves a binding from the resource part to a borrow
part (mutable or immutable). This part of the formalization is
unfortunately a bit opaque as it is hidden in the environment
formation (L 2113-2123).
The Region typing rule transforms the typing context (for example, L
2375); the corresponding transformation of the run-time environment is
left implicit.

We will try to improve the writeup for this issue in the revision.

> The proof of F.2 seems to omit the cases of the semantics that might
> modify the heap

We put the cases that we felt were most important.

> I cannot find type rules for Create/Observe/Destroy in the supplementary material (my apologies if I missed them somewhere).

That's an unfortunate editing mistake.

# Reviewer B

## Modules

Affe's usage of subsumption also interacts with type abstraction and modules
For instance, the `File.t` type presented in Section 1 could be implemented
as a file descriptor (i.e., an integer), which is unrestricted. Subsumption
then allow the unrestricted type to be exposed as affine.
Such mechanism allow programmers to implement their own primitives on
abstract types. Programmers are then in charge of ensuring soundness of such primitives. This feature, which is also present in Alms, allows to partially emulate Rust's `unsafe` construct.

# Reviewer C

## Simplification and subkinding

The reviewer ignores Affe's use of subsumption which allows us to
simplify many type signatures without loosing expressiveness.
In particular, as highlighted in section 1.1, the compose function

    let compose f g x = f (g x)
    # compose : (k <= k1) => (b -k-> c) -> (a -k1-> b) -k-> (a -k1-> c)

admits having `f` linear and `g` affine with a linear outcome:
Because affine is a subkind of linear, `g`'s multiplicity can be subsumed to
linear, both k and k1 are instantiated to linear, and the resulting
function type is annotated as linear. This approach follows the
treatment of structural subtyping in HM(X).

## Regions and borrowing

The session types interface that we present is using a functional
style with linear types to demonstrate that this application is in
scope of our system and that  Affe's type inference
handles it gracefully, without extra annotations.

Borrows are more useful for imperative
programming and we are not claiming to apply them to session types.
As explained in Section 2.3, the goal of Affe is to support both
styles, allowing the programmer to choose the most appropriate one for
the task at hand. 

Dealing with borrows for session-typed channels would require a major
extension with typestates, which is notoriously incompatible with type
inference. 
However, one could contemplate operations to extract channel metadata
(IP , bytes sent, etc) from a shared borrow of a channel as in 
`get_address: &(_ channel) -> ip_address`, 
which is typable in Affe.
As the main reference to the channel cannot be used while a borrow is active, such
operations would be sound.

## Formalization

We disagree that the formalization is incomplete.
In particular, the handling of the range of borrows is detailed in Section 3.2.4 on regions.
Furthermore, the lack of deconstruction form for borrows of abstract types is
intended: only the appropriate primitives can act on borrows, because the semantics
of borrow is specific to a given abstract type: For instance the
shared borrow in `read_line : &file -> string` may lead to data races,
whereas `&!file -> string` doesn't.

For space reasons and because the current article focuses on linearity, borrowing,
and inference, we decided not to detail the handling of matching on pairs.
We agree that such aspect is important, and we will expand on this
topic if the article is accepted. 

> Related work

Correct, Quill comes with a usage-counting semantics. What we meant to
say is that their semantics isn't store based.

Alms is a seminal work that supports many interesting examples, but it
comes with a heavy price in terms of complexity (e.g., dependent
kinds, lub operator in types) and it is not suitable for type
inference. Most of the examples in the Alms paper exploit the
genericity of existentials to, e.g., connect resources with
capabilities. In order to provide full type inference
Affe doesn't have unrestricted existentials, and the
corresponding examples are unlikely to work in Affe as they are stated
in the Alms paper.

The examples in section 2 are not aimed at comparing with Alms, rather
we want to demonstrate that the idea put forward in the Alms paper (to
annotate abstract types in module signatures) also works with Affe's
type inference.

We will insert a citation of the Gan, Tov, and Morrisett paper with
the copy-on-write array.


# Reviewer D

> Partial inference and GADT

Even if a language does not admit full type inference, we believe, 
there should be a well-defined core language which does.
This way, a programmer who steps over the boundary knows when type
annotations are needed.
In particular, it is possible (and desirable) to extend Affe with existential types
by requiring type annotations, similarly to Alms.
The results we present nevertheless garantee that
full type inference is supported in the absence of existentials.

> the paper would strongly benefit from more examples that explain why the type inference algorithm works the way it does.

One such example is available for constraint solving in the Appendix B.1, but we agree
that it should be extended, and part of the main body.
