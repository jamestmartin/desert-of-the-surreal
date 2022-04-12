# Realizability
The logics described by our [framework](framework.md) correspond with type theories and programming languages
via a generalized realizability interpretation.

## The Meaning of Proofs
The Curry-Howard correspondence describes the direct relationship between type theory and formal logic.
The realizability interpretation gives us the meaning of proofs in intuitionistic logics
and type theories can be used to describe the interpretation of proofs as programs
and type theories (and consequentially, formal logics) as programming languages.

Here we will be translating logics into type theories and programming languages
which are not usually treated in this way, including:
* the theories of the basic cube, including basic, classical, and dual intuitionistic logics
* the co-symmetric theories in the co-basic cube

### Intuitionistic Type Theory
I will assume that you are already familiar with how these interpretations apply to intuitionistic theories,
although I will restate some facts here for comparison.

In intuitionistic type theory, a context `Γ` is a list of variables and types `x₁ : A₁, x₂ : A₂, ...`.
A typing derivation `Γ ⊢ x : A` corresponds with a deductive proof, `x`, of the interpretation of the type `A` as a proposition
under the context of assumptions `Γ`.

Observe the asymmetry between the left-hand side and the right-hand side of the entailment.
The left-hand side assigns types to variables whereas the right-hand side assigns types to terms.
Thus, all of our operational rules are defined as manipulating terms on the right-hand side.

We expect generally that types are described by some form of induction (well-foundedness).
A term of an inductive type `A` are in canonical form if they are constructed explicitly by the type's constructors
(correspondingly by operational rules introducing the type on the right-hand side of the turnstile).
For example, a canonical term of the natural number type is a sequence of applications of the successor to zero.

We compute with terms of an inductive types using eliminators, which use terms of type `A`
to construct proofs of types other than `A`.
We may also define types using coinduction, but coinduction results in weaker types in intuitionistic type theory than induction.
(TODO: Clarify, elaborate.)

All terms `⊢ x : A` may be reduced to a normal form of `A`; proofs `Γ ⊢ x : A` will more generally be reduced to canonical forms.
This means that a term `x : A` is not only a proof of the mere existence of `A`, but an actual value of type `A`
which is the result of running our program.

Intuitionistically, a proof of implication `Γ ⊢ λx.e : A → B` is constructed from a proof `Γ, x : A ⊢ e : B` and thus reflects entailment.
It is eliminated via `Γ ⊢ f : A → B` and `Λ ⊢ x : A` entails `Γ, Λ ⊢ f x : B`.
We then define `¬A` as `A → ⊥`, thus giving us `Γ, x : A ⊢ e : ⊥` entails `Γ ⊢ λx.e : ¬A`.
Thus classically, we define implication in terms of negation; intuitionistically, we define negation in terms of implication.

In some logics, such as classical logic, you have a negation connective,
described with rules like `Γ, A ⊢ B, Δ` entails `Γ ⊢ ¬A, B, Δ`.
We can use this rule to construct `Γ ⊢ ¬A ⅋ B, Δ` and define implication, `A → B`, as `¬A ⅋ B`
thus giving us `Γ ⊢ A → B, Δ`.

This does not work naively in intuitionistic type theory because of the asymmetry of contexts.
Even assuming for a moment that we were to allow multiple terms on the right-hand side,
we would expect the right-hand side to include a term of type `x : ¬A`,
but the assumption of type `A` was a variable, not a term, so there is no "information"
there for us to use to construct a term.

However, because `⊥` is uninhabited, we can conlude that a term of type `¬A` will never be applied to a value of `A`,
meaning that the way in which `¬A` is proved is completely irrelevant. It is sufficient to know *that* we have proved `¬A`;
the details of the proof may be discarded. Relatedly, the only purpose of a term of type `¬A` is to prove the non-existence
of terms of type `A`, such as to forget about an impossible branch of a pattern-match.

Thus, a term of type `A` may be reduced to a value of type `A`, whereas `¬A` is a proof of the mere non-existence of a proof of `A`.

So if `¬A` is "mere existence" and we can discard the details of the proof,
then why does it matter that we don't know how to construct it?
Why can't we just invent some dummy placeholder term?
Consider what our rules would look like in terms of a single term on the right-hand side:

If we're forced to provide `B`, then we get `Γ, x : A ⊢ e : B` entails `Γ ⊢ λx.e : ¬A ⅋ B`.
Alternatively, if you're not forced to provide `B`, then we get `⊢ em : ¬A ⅋ A`.
Both of these are bad, but I'll begin with the first.
   
All of our *other* rules can, and indeed do, operate on *one* term on the right-hand side.
Thus, there is *no* way to construct a term with a right-hand side which is not exactly one term.
But consider the formation rule for `⅋`: `Γ ⊢ A, B` entails `Γ ⊢ A ⅋ B`. This requires *two*
terms on the right-hand side, and therefore there is *no* other way for us to
construct a term of type `A ⅋ B`!
   
On the other hand, the eliminators for `⅋` correspond with disjunctive syllogism.
`Γ ⊢ A ⅋ B` entails `Γ ⊢ ¬A → B` and `Γ ⊢ ¬B → A`. What conclusions can we use this to draw
from our introduction rule?
1. `¬B → ¬A`. We can already prove this with the implication version.
2. `¬¬A → B`. Compared to implication, this is equivalent to the excluded middle, `¬A ⅋ A`. This is *very bad*.

We've already established that `¬A` is irrelevant and provides no information for all `A`, and so is `¬¬A`. (TODO: Explain why.)
If we used `λ`, then `B` is defined in terms of computing against `A`,
so we have no information to use to construct our term of type `B`.
Alternatively, if we used `em`, then we have no information, period.
Therefore, if we use `⅋` to define `→`, we can no longer reduce `B` to canonical form, for all `B`.
Therefore, any `B` can at most consistute mere existence of a `B`, not an actual value of `B`.

The above points may have seemed unnecessary, and perhaps even obvious.
However, making explicit the asymmetry of entailment and the distinction
between existence, mere existence, and mere non-existence is necessary
to explain the proof semantics of the rest of our type theories.
(It will only continue to grow deeper.)

Side-note: although morally, `¬A` is irrelevant, in programming languages which
take some liberties in their correspondence with type theory (e.g. languages like Haskell),
it is not necessarily entirely irrelevant; it may perform side-effects or get caught in an infinite loop.
Of course, it makes no difference in a consistent theory, but many programming languages are inconsistent
because many forms of inconsistency (such as turing-completeness) are desirable from a programming point of view,
while having relatively small harmful effects for the most part.

### Dual Intuitionistic Type Theory
Dual intuitionistic type theory is described by entailments `x : A ⊢ Δ` where `x` is a coterm of type `A`
and `Δ` is a context of copremises which assign types to covariables.

Okay, so what is all of this "co" nonsense. First of all, a coterm looks *exactly* like a term.
It's a tree which represents a deductive proof, just like terms are trees represent deductive proofs.
The *only* difference is that whereas a term is a semantically proof of something on the *right*-hand side of the context,
coterm is semantically a proof of something on the *left*-hand side.

So what does it mean to prove something on the left-hand side?
A coterm of type `A` is like a term of type `¬A` in that it has a canonical form,
and that it's a statement about how to get rid of an `A`.
However, whereas a term of type `¬A` proves the *mere* non-existence of `A`,
a coterm of type `A` describes the *actual* non-existence of `A`.

However, non-existence isn't the whole picture, so I should explain what the *actual* part means.
A coterm of type `A` isn't so much a proof that `A` is impossible as a procedure to *eliminate* an `A`.
If `A` contains negative types such as `¬B` (which are comparable to terms of type `¬¬B` in intuitionistic type theory),
then in reality we are not describing a proof of non-existence so much as
a means to deconstruct an `A` into a `B`.
It gives us a way to concretely describe the ways in which a (co)inductive type may be eliminated.

It's unintuitive, and I don't know what to say to magically make it make sense.
I suggest that you bang your head against the rules and examples until it makes sense;
if you're lucky, then someone has written a nice blog post or Q&A site answer
of a higher-quality than "a coterm is like a burrito...".

To understand what a coterm looks like, it may help to look at its canonical form.
A coterm is in canonical form if it is constructed explicitly from the type's *eliminators*.

Note that in intuitionistic type theory, a type's eliminators are quantified over implication, for example
`∀ C → (A → C) → (B → C) → A ⊕ B → C`. This awkwardness is a result of being restricted
to single terms on the right-hand side, but dual intuitionistic eliminators are not so awkward.
Although this **is not the actual rule**, the dual intuitionistic eliminator
looks more similar to the intuitionistic type `¬A → ¬B → ¬(A ⊕ B)`.
Conversely, dual intuitionistic constructors are awkward in the same way intuitionistic eliminators are awkward.

Thus, syntactically, a canonical coterm strongly resembles a canonical term.
In fact, it strongly resembles the constructor of its intuitionistic dual, specifically.

For the same reasons as intuitionistic type theory, `¬A` represents mere evidence regarding `A`.
However, whereas in intuitionistic type theory `¬A` is mere evidence for the *non*-existence of `A`,
in dual intuitionistic type theory, `¬A` is mere evidence for the *existence* of `A`,
similarly to intuitionistic type theory's `¬¬A`.

Dual intuitionistic's native form of implication is actually `A / B`
(read "A excludes B" and written by some other authors as `←` or `−`), not `→`.
Classically, `A / B` is defined as to `A ⊗ ¬B` (keeping in mind that everything is negative here
relative to intuitionistic logic; in intuitionistic logic, we would have `A / B` as comparable to `¬(A ⊗ ¬B)`).

A dual argument to intuitionistic logic about the problems of various connectives applies to dual intuitionistic logic.
In particular:
* `⊗` is useless, but on the other hand,`⅋` is a perfectly functional connective in dual intuitionistic logic, thank you very much.
* Double negation introduction `¬¬A / A` and non-contradiction `A ⊗ ¬A` are problematic,
  whereas `A / ¬¬A` and the excluded middle `A ⅋ ¬A` are theorems.

TODO: Explain `→` in dual intuitionistic logic, and the new connective, `/`, in intuitionistic logic.
Is it boring and equivalent to `¬(¬A ⅋ B)`, or is it an exciting way to describe an
analog to that type which constitutes actual evidence rather than mere evidence?

### Structural Basic Type Theory
TODO: This is a stub.

In basic type theory, both the left-hand side and the right-hand side of entailment correspond with (co)terms.
`x : A ⊢ Δ` is a coterm, whereas `Γ ⊢ x : A` is a term. Both represent actual evidence.
Both have canonical forms corresponding with their canonical forms in (dual) intuitionistic type theory.

`¬A` still represents mere evidence, but interestingly enough, there are two inequivalent negations:
`A → ⊥`, intuitionistic negation, and `1 / A`, dual intuitionistic negation.
Due to handedness of the implications, intuitionistic negation tends to have semantics on the right-hand side
whereas dual intuitionistic negation has semantics on the left-hand side, where
they respectively represent mere non-existence, and mere existence.

Connectives are diminished in strength relative to their (dual) intuitionistic counterparts.

Basic type theory is very weak, but it is interesting because of its
compatibility with both intuitionistic and dual intuitionistic type theory.

### Classical Linear Type Theory
TODO: This is very incomplete and in dire need of clarification and elaboration.

In classical linear type theory, because of the ambidexterous context,
proofs no longer can be described in terms of tree-shaped terms; instead, terms must be represented as an acyclic graph.

Classical linear type theory no longer has canonical forms in general,
and intermediate reductions (applications of cut) no longer necessarily have representations as terms. (TODO: Verify.)
However, interestingly, closed terms and coterms which correspond with types in (dual) intuitionistic type theory
(i.e. no `⅋` or resp. `⊗` or `¬`) *still keep their canonical forms*!

This is because of how we assign computational semantics to LEM and NC.
Terms of `A ⅋ B` or `A ⊗ B` correspond semantically with threads and synchronous messaging (or coroutines).
Types correspond with channels. `lem : ⊢ ¬A ⅋ A` creates two threads and a channel `¬A ⅋ A` which they use
to communicate. `nc : ¬A ⊗ A ⊢` sends a message of type `A` (represented like a term) to the channel `¬A`, or alternatively,
a message of type `¬A` (represented like a coterm) to the channel `A`.
More generally, you can use an eliminator (resp. constructor) to reduce a type `¬A` (resp. `A`) to a smaller type without satisfying
the entire channel all at once, so messages are synchronous. If a type contains negations, it represents a
back-and-forth synchronous communication between the threads instead of entirely unidirectional.
Dependent types can be understood as messages whose content depends on previous messages,
which is how message-passing usually works in practice.

Anyway, because of linearity, you cannot simply *discard* a `¬A` introduced by LEM.
If a `¬A` does not occur in the type of a closed (co)term, then that means it necessarily has
been satisfied, and the corresponding thread has terminated and fully produced a value of type `A`.
Thus, if a (co)term does not contain any `¬A` constructed in this manner, it may be understood
as single-threaded and be fully determined according to the appropriate (dual) intuitionistic interpretation.

I would strongly suggest reading up on the game semantics and resource semantics of classical linear type theory,
and additionally the pi calculus to get an intuition for how this works.

In classical linear type theory, implications are equivalent to `⊗` and `⅋` together with `¬`,
and in this way collapse. (TODO: Verify.)

### Classical (Structural) Type Theory
TODO: This is a stub.

In classical (structural) type theory, proofs can no longer be described in terms of tree-like terms.
Terms no longer necessarily reduce to canonical forms at all;
we may still apply the trick about message passing used by classical linear type theory
to get *many* applications of LEM and NC to reduce, which is helpful for working with dependent types,
but it no longer always works.

In general, proofs in classical type theory represent mere evidence.

### The Relationship Between Type Theories
Proofs in basic type theory:
* Any proof in the form `Γ ⊢ x : A` is a proof in intuitionistic type theory.
* Any proof in the form `x : A ⊢ Δ` is a proof in dual intuitionistic type theory.
* Any proof in the form `Γ ⊢ Δ` is a proof in classical type theory.
* Any proof of the form `Γ ⊢ x₁ : A₁, ...` is a proof of `Γ ⊢ A₁ ⊕ ...` in structural intuitionistic type theory. (TODO: Verify.)
* Any proof of the form `x₁ : A₁, ... ⊢ Δ` is a proof of `A₁ & ... ⊢ Δ` in dual intuitionistic type theory. (TODO: Verify.)

Proofs in (dual) intuitionistic type theory (TODO: verify):
* Any proof of the form `Γ ⊢ x : A` in intuitionistic type theory is a proof of `x : ¬A ⊢ ¬Γ` in dual intuitionistic type theory.
* Any proof of the form `x : A ⊢ Δ` in dual intuitionistic type theory is a proof of `¬Δ ⊢ x : ¬A` in intuitionistic type theory.
* Any proof in (dual) intuitionistic type theory is a proof in classical type theory.
* TODO: Specific proofs in (dual) intuitionistic type theory should correspond with eliminators (constructors)
  in the dual theory. Perhaps, in fact, eliminators (constructors) could be *defined*
  as a special case of the translation from the dual theory?

Proofs in classical linear type theory (TODO: figure out the details & verify):
* Many proofs of the form `Γ ⊢ x : A`, especially where `Γ` contains neither `⅋` nor `¬`,
  correspond with proofs in intuitionistic type theory.
* Dually for dual intuitionistic logic.

Proofs in substructural type theories in general:
* Any proof in a substructural type theory is a proof in the corresponding structural type theory.

TODO: A logic `A` which is strictly stronger than a logic `B` may be embedded into `B`
by introducing a modality connective or implication connective (reflecting the entailment of `A`)
and restricting the way `A`-implication can influence proofs in `B` (for example,
classical logic embedded into intuitionistic logic must be placed in a proof-irrelevant
box such as Prop or propositional truncation, where it is restricted to acting as mere evidence).
However, this is a result of the framework, not realizability.

## Term Syntax

## Typed Conversion
