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

### Dual Intuitionistic Type Theory

## Term Syntax

## Typed Conversion
