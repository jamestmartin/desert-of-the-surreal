# The Framework of Implications
A broad class of logics and their implication connectives may be described in terms of combinations of a small set of properties and symmetry.

## The Properties
The properties which we use to categorize implications are the following:
1. preservation: truth-preserving, falsity-preserving, or degree-preserving
2. axioms: paraconsistent, paracomplete, or both paraconsistent and paracomplete
3. structurality: structural, substructural, or non-structural
4. context-handedness: classical, intuitionistic, dual intuitionistic, or basic

These properties may be used to describe implication, which reflects entailment and negation;
some of these properties characterize entailment while others describe negation.

### Preservation
Preservation is a property of entailment describing the relationship
between the strength of the premises and the strength of the conclusion.

#### Truth-preserving
If `Γ ⊢ Δ`, then `Δ` is at least as true as `Γ`.
Proofs concluding in truth-preserving entailment correspond with deduction.

This most likely corresponds with most logics and type theories you are familiar with.

Connectives which reflect truth-preserving entailment, such as (double) negation in intuitionistic logic
have this property: `A → ¬¬A`.

#### Falsity-preserving
If `Γ ⊢ Δ`, then `Δ` is at most as true as `Γ`.
Proofs (or more accurately, refutations) concluding in falsity-preserving entailment correspond with codeduction.

Codeduction may be intuitively explained as the form of reasoning used by the scientific method.
This form of reasoning is explained intuitively and concisely by [Richard Feynman's lecture on the scientific method](https://www.youtube.com/watch?v=EYPapE-3FRw).

In some sense, when reasoning using a falsity-preserving logic, you begin with a hypothesis (your premise)
and try to discover the consequences of that hypothesis (your conclusion),
with the goal of finding out the ways in which your hypothesis may be wrong,
so that you may reformulate your hypothesis in a way such that it will no longer be wrong.

Connectives which reflect falsity-preserving entailment, such as (double) negation in cointuitionistic logic,
have this property: `¬¬A → A`.
(TODO: Verify.)

#### Degree-preserving
If `Γ ⊢ Δ`, then `Δ` is precisely as true as `Γ`.

Degree-preserving entailment allows neither proving a true conclusion from a false premise
nor refuting a false conclusion from a true premise.

In addition to being compatible with both truth-preserving and falsity-preserving modes of reasoning,
degree-preserving entailment may also preserve more sophisticated truth values than "true" or "false".
(TODO: Elaborate.)

### Axioms
The property of axioms describes which variants of the identity axiom are valid.

There are multiple variants of the identity axiom, described by [Paracomplete Logics Dual to the Genuine Paraconsistent Logics: The Three-valued Case](https://www.sciencedirect.com/science/article/pii/S1571066120300827). Examples include:
* Identity: `A ⊢ A`
* Non-Contradiction:
  * NC: `A, ¬A ⊢`
  * NC': `⊢ ¬(A ∧ ¬A)`
* Excluded Middle:
  * EM: `⊢ A, ¬A`
  * EM': `¬(A ∨ ¬A) ⊢`
* Universally quantified variants, including these examples from intuitionistic type theory:
  * `∀ A → A ∨ ¬A`: the excluded middle, realized by undelimited continuations.
  * `¬¬(∀ A → (A ∨ ¬A))`: the double-negated excluded middle, equivalent to double negation shift, and realized by delimited continuations.
  * `∀ A → ¬¬(A ∨ ¬A)`: a principle which looks like the excluded middle, but which is a theorem in intuitionistic type theory.

Note that non-contradiction does not necessarily correspond with explosion.
An empty right-hand context corresponds with the falsity `⊥`,
but the principle of explosion corresponds with the falsity `0`,
and the two negations do not necessarily coincide.
(TODO: Elaborate.)

Implication reflects a weak form of non-contradiction whereas exclusion reflects a weak form of excluded middle.
Negations may be written in terms of implications, either `A → ⊥` or `1 / A`.
The excluded middle and non-contradiction cause implications to decompose into dis/conjunction and negation,
but are not solely sufficient on their own; structural rules are also necessary.
(TODO: Verify, clarify, elaborate.)

#### Paraconsistent
In paraconsistent theories, NC does not hold in general.

#### Paracomplete
In paracomplete theories, EM does not hold in general; NC may hold.

EM has a harmful effect on the equational theory for affirmations,
so proof-relevance is a desirable property which is realized better in paracomplete systems than classical systems.
(TODO: Clarify, elaborate.)

#### Paraconsistent and Paracomplete
In paraconsistent and paracomplete theories, neither NC nor EM holds in general.

These systems have nice properties which I'll get into elsewhere.
(TODO: Elaborate.)

### Structurality
Structurality describes which structural rules hold. The structural rules are (in a system with contexts on both sides):
* Contraction:
  1. If `Γ, A, A ⊢ Δ` then `Γ, A ⊢ Δ`.
  2. If `Γ ⊢ Δ, A, A` then `Γ ⊢ Δ, A`.
* Weakening:
  1. If `Γ ⊢ Δ` then `Γ, A ⊢ Δ`.
  2. If `Γ ⊢ Δ` then `Γ ⊢ Δ, A`.
  
#### Structural
In structural systems, both contraction and weakening hold.

#### Substructural
In substructural systems, either only one of contraction and weakening hold,
or contraction and weakening may be restricted to only one side of the context.

There is some sort of interaction between which structural rules
combined with which context-handednesses and axioms gives interesting results,
but the details are not yet clear.

Some of these results are described in another document.
(TODO: Verify, clarify, elaborate.)

#### Nonstructural
In nonstructural systems, neither contraction nor weakening hold.

### Context-handedness
Our primary reference for context-handedness is ["Basic logic: reflection, symmetry, visibility."](https://www.math.unipd.it/~sambin/txt/SBF.pdf).

Context-handedness results in additional left-handed and right-handed cuts,
which may correspond with call-by-value and call-by-name evaluation strategies respectively.

TODO: Write this section.

#### Classical
Systems which liberalize the context on both sides loosely correspond with classical logics,
although this does not imply that either excluded middle or non-contradiction hold.

#### Intuitionistic
Intuitionistic logics liberalize the context on the left side.

#### Dual-intuitionistic
Dual-intuitionistic logics liberalize the context on the right side.

#### Basic
Basic logics liberalize the context on neither side.

## Logics & Symmetries
TODO: Write this section.

* truth-preserving: LK, LJ = BSL, LDJ = BSR, CLL = BLR, B, BS, BL, BR
* false-preserving: coLK, coLJ, coLDJ, coCLL, coB, coBS, coBL, coBR
* categorize: Lq, Lnq, coLq, coLnq, L<=, coL<=, fill in rest

We conjecture the existence of several logics outside these, including those with:
* substructurality without non-structurality
* imaginary or complex-degree preserving entailment
  * may be related to interval types; Lnq may be related to higher paths
  * alternative logics sitting at the "top" adjacent to systems like LK, e.g. LJ with intervals
* unclear how fuzzy logics fit in

The framework may need to be generalized to fit some of these proposed extensions
in addition to the new logics which the framework appears to predict.
