# Big conjectures Part 1
## Overview
Here are my big conjectures:
1. There is a trichotomy between equational theory, computation, and polarity.
2. Eta laws remove polarity in intuitionistic and dual intuitionistic theories as structural laws remove it from linear theories.
3. These trade-offs together encompass the relationship between a broad variety of existing type theories and logics.

### Conjecture 1
There is a trichotomy between equational theory, computation, and polarity. The perfect classical type theory does not exist. You can:
1. sacrifice your equational theory
   1. by letting it be equationally consistent, making dependent types inconsistent
   2. by abandoning some forms of extensionality, making dependent types weaker (??? if this makes sense)
2. sacrifice computation for axioms and make the identity type trivial
   1. abandon computation entirely
   2. package axiom(s) into an irrelevant box (e.g. definitionally proof-irrelevant Prop or propositional truncation)
      * which axiom you box depends on whether the greater theory is intuitionistic, dual intuitionistic, or linear
3. introduce polarity in a way which constrains the use of axioms
   1. make the theory paracomplete (accept non-contradiction (NC); weaken eta rules for `⅋`)
   2. make the theory paraconsistent (accept LEM; weaken eta rules for `⊗`)
   3. make the theory substructural and
      1. weakly paraconsistent (accept LEM; abandon contraction) (are 3.3.1 and 3.3.2 mixed up slightly?)
      2. weakly paracomplete (accept NC; abandon weakening)
      3. weakly paracomplete and weakly paraconsistent (accept NC and LEM; abandon weakening and contraction)

There are **more** trade-offs in the trichotomy to be made in weaker theories; I will get into some of these in a later section.

Here are some more examples of theories which I believe realize some of these tradeoffs:
1. related: https://proofassistants.stackexchange.com/q/541/788, fire triangle, call-by-push-value
   1. 𝜆𝜇-calculus
   2. ??? (some sort of dependent CPBV, with nasty semantics like GHC Haskell?)
2. related: https://proofassistants.stackexchange.com/q/965/788, https://proofassistants.stackexchange.com/q/1153/788
   1. MLTT or CIC with LEM as an axiom (an intermediate version has UIP/axiom K or propositional resizing)
   2. Definitional Proof-Irrelevance without K (Prop/SProp in Agda/Coq respectively)
      * This represents the intuitionistic perspective on this approach specifically. (LEM implies impredicativity, btw.)
3. related: basic type theory, linear type theory
   1. Intuitionistic (basic) type theory, MLTT, or CIC
   2. Dual intuitionistic (basic) type theory
   3.
      1. ???
      2. ???
      3. Classical linear (basic) type theory

### Conjecture 2
Eta laws remove polarity in intuitionistic and dual intuitionistic theories as structural laws remove it from linear theories:
* Implication and exclusion are the result of adding structural rules without adding eta rules.
* Function extensionality is a weak form of the eta rule for `⅋`; it has to be added back because intuitionism removes it.
  * A dual argument applies to exclusion and `⊗`.

### Conjecture 3
These trade-offs together encompass the relationship between a broad variety of existing type theories and logics.
* Almost any combination of these theories has a non-trivial greatest lower bound (i.e. a theory whose proofs are valid in all parents)
* There are theories described in this way which are stronger than (few) and weaker than (many) any theory which has been described, to my knowledge.

## The intuitionistic perspective
This following section describes the relationship between LEM, NC, eta laws, and structural laws in intuitionistic type theory:

```agda
-- requires weakening
weak⊗ : A ⊗ B → A & B
π₁ (weak⊗ (x₁ , x₂)) = x₁
π₂ (weak⊗ (x₁ , x₂)) = x₂

contr& : A & B → A ⊗ B
-- requires contraction
contr& x = (π₁ x , π₂ x)
   
eta& : (x : A & B) → weak⊗ (contr& x) ≡ x
-- requires eta reduction or propositional eta equality for `&`
eta& _ = refl

eta⊗ : (x : A ⊗ B) → contr& (weak⊗ x) ≡ x
-- requires eta reduction or propositional eta equality for `⊗`
eta⊗ (_ , _) = refl
```

Observe that weakening and contraction are required to show that `⊗` and `&` imply each other,
but it takes their eta laws to show that the functions are an equivalence.
Thus by removing any, we get a theory in which these types are inequivalent.

```agda
postulate lem : (¬ A) ⊕ A

weak→ : (A → B) → (¬ A) ⊕ B
-- requires excluded middle
weak→ x with lem
-- requires weakening
... | σ₁ ¬A = σ₁ ¬A
... | σ₂ A = σ₂ (x A)

contr⊕ : (¬ A) ⊕ B → (A → B)
-- requires non-contradiction & ex falso
contr⊕ (σ₁ ¬A) = λ A → exfalso (¬A A)
-- requires weakening
contr⊕ (σ₂ B) = λ _ → B
```

Observe that one direction requires LEM and the other requires NC,  but *both* require weakening and *neither* require contraction.
Thus removing any is sufficient to get a system where they do not imply each other.

```agda
postulate fun-ext : (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g

eta⊕ : (x : (¬ A) ⊕ B) → weak→ (contr⊕ x) ≡ x
eta⊕ {A = A'} x with lem {A'}
-- requires function extensionality
eta⊕ {A = A'} (σ₁ x) | σ₁ ¬A = cong σ₁ (fun-ext ¬A x λ _ → ⊥-prop)
eta⊕ {A = A'} (σ₁ x) | σ₂ A = exfalso (x A)
eta⊕ {A = A'} (σ₂ x) | σ₂ A = refl
-- we have `A → B` and `A → ⊥` but not `B → ⊥`
eta⊕ {A = A'} (σ₂ x) | σ₁ ¬A = {!!} -- σ₁ ¬A ≡ σ₂ x

eta→ : (x : A → B) → contr⊕ (weak→ x) ≡ x
eta→ {A = A'} x with lem {A'}
-- requires function extensionality
... | σ₁ ¬A = fun-ext (λ A → exfalso (¬A A)) x (λ A → exfalso (¬A A))
-- we do not have `∀ (x : A') → x ≡ A` (this would imply that all types are propositions)
... | σ₂ A = {! !} -- (λ _ → x A) ≡ x
```

Although LEM, NC, and weakening will get them to imply each other, no consistent equations will make them equivalent.
Without sacrificing any of our logical strength, we can add LEM by:
1. arbitrarily choosing an evaluation order, which leads to 1.2 (unclear)
2. abandoning computation, yielding 2.1 (MLTT+LEM) (you are here)
3. putting LEM in a Box, yielding 2.2 (Prop or LEM₋₁)

We can also add LEM by abandoning some of the logical strength of our system:

4. abandon dependent types so that equational consistency doesn't matter, yielding 1.1 (𝜆𝜇)
5. weakening LEM, yielding 3.1 (MLTT) and leaving us right back where we started
6. abandon weakening (3.3.2)

For the most part, all of those options should be fairly easy to understand.
More confusingly, we can go in a wildly different direction and pivoting to dual intuitionism or classical linear theories,
which yield 3.2, 3.3.1, 3.3.3, and different variants of 2.2.

## The weaknesses you didn't even know intuitionistic type theory had
I'm going to elaborate some more trade-offs indicated by the trichotemy conjecture:
1. Intuitionism and dual intuitionism have weaker eta laws than classical linear theories.
2. Intuitionism and dual intuitionism trivialize computation and identity types for half of all types (resp. positive and negative types).
3. A theory can be substructural in multiple ways, depending which set of structural and eta laws it chooses.
4. Futhermore, you can choose weaker systems whose proofs hold in multiple of the above stronger systems.

As a specific example, the usual intuitionistic type theory:
1. weakens negative dependent types and eta laws for `⅋` (and abandons `←`)
2. trivializes refutation and the negative identity type; double negation doesn't compute properly
3. divides `+` into `⊕` and `→`, weakens the eta laws for `→`, abandons `←` and `⅋`
   * function extensionality is *propositional* and has to be added back as an *axiom*
4. cannot transfer its proofs to dual intuitionistic or substructural type theories

### De-trivializing the trivial
As I mentioned before, in intuitionistic type theory, `¬` and `Id ¬` are trivial. It doesn't have to be this way; I'll explain in terms of data, computations, and triviality.

**NOTE: EVERYTHING BELOW HERE IS INCOMPLETE.** This is the section where I should be explaining the informal justification for my conjectures, but it is just too much to write down right now. I have spent the last day doing basically nothing but writing and I need to move on for a while. Instead, I will copy/paste stuff from an older draft because it's better than nothing. (I may write a follow-up later, and you can always ask me questions.)

In intuitionistic type theory:
* `A ⊗ B`  is an A and a B together "in memory", like a struct; `1` is the empty struct.
* `A ⊕ B` is a bool followed by an A or a B "in memory", like a tagged union; `0` is the empty union.
* `A → B` does not have a value "in memory"; it is encoded as code, and some data (if it is a closure); `⊥` is a crashed program.
* `A & B` may also be represented as code (two functions and shared data); `⊤` has no code, just data (which we will be forced to discard).
* `⊗` and `&` are equivalent and usually written ambiguously as `×`; `⊕` is usually written `+`.
* `¬A` is defined as `A → ⊥`, so it ought to be represented as a closure. But `⊥` is a proposition, so by functional extensionality, so is `A → ⊥`, making it trivial. Logically, we know this means it (morally) has no representation at all, like `1` or `0`. On the other hand, any Haskell programmer could tell you that it is indeed a closure and not trivial at all.

For simplicity I'll write types from the perspective of intuitionistic type theory, i.e. where all terms and types are of the form `Γ ⊢ x : A`. Morally, dual intuitionistic TT should be presented dually, with `x : A ⊢ Δ`, and the rules are a *lot* cleaner that way, but I will be sticking to the ITT perspective to avoid confusing people who are only familiar with ITT. In dual ITT, none of these types are actually negative, but on the other hand negative dual ITT types behave far more closerly to ITT types and vice versa.

In dual intuitionistic type theory:
* `¬(A ⅋ B)` is a ¬A and a ¬B together "in memory", like a struct; `¬⊥` is the empty struct.
* `¬(A & B)` is a bool followed by a ¬A or ¬B "in memory", like a tagged union; `¬⊤` is the empty union.
* `¬(A ← B)` is encoded as code and some data (if it is a closure).
* `¬(A + B)` is encoded as a pair of functions and the data they close over.
* `⅋` and `⊕` are equivalent and usually written ambiguously as `+`; `&` is usually written just `×`.
* there is another kind of negation `1 ← A` which behaves strangely because of the decision to make things "simpler" by writing types from the perspective of ITT.

bear with me as I break things down some more... let's now visit classical linear type theory:
* you have two product types: `A ⊗ B` and `A & B`.
* you have two sum types: `A ⊕ B` and `A ⅋ B`.
* you have two... one...? zero...? function types. `A → B = ¬A ⅋ B`. `A ← B = A ⅋ ¬B`.
  * LEM holds; `1 ⇒ ¬A ⅋ A` and `1 ⇒ A ⅋ ¬A` (`⇒` is implication in the meta-theory, more-or-less)
  * non-contradiction (henceforth NC) holds; `A ⊗ ¬A ⇒ ⊥` and `¬A ⊗ A ⇒ ⊥`

but LEM and NC aren't enough to characterize function types or par, now, are they?

intuitionistic & dual intuitionistic linear type theory:
* `A → B` should still be `¬A ⅋ B`, but it's obviously not. we have `A → A` but not `¬A ⅋ A` because that's literally just LEM.
* dually, `A ← B` should be `A ⅋ ¬B`, but `A ⊗ ¬(A ← B) ⇒ ¬B` would become `A ⊗ (¬A ⅋ ¬B) ⇒ ¬B` and then `(A ⊗ ¬A) ⅋ ¬B ⇒ ¬B`, which is just NC.

so what's the *actual* rule for function introduction (resp. exclusion elimination)? `λ`. not LEM, not NC, but `λ`.
* what is `λx. e : A → B`, syntactically? it binds a variable `x : A` in the term `e : B`... only `e` doesn't really have type `B`, because of the `A` missing in the context.
  so `e`, syntactically, is a term derivation of type `x : A ⊢ e : B` (in some broader context Γ shared by λ)
* dually you have `λ₂x. e : ¬B ← ¬A`. `x : ¬A ⊢ e : ¬B`, which by duality is really just `e : B ⊢ x : A`.

note that the elimination rule for functions is still (morally) NC and the introduction rule for exclusion is still (morally) LEM.
knowing this, let's try giving some better rules for classical `⅋`:
* `λ₁x. e : A → B` constructs `1 ⇒ ¬A ⅋ B`; `1 ⇒ ¬A ⅋ A` (LEM) trivially follows
* `λ₂x. e : ¬B ← ¬A` eliminates `¬B ⊗ A ⇒ ⊥`; `A ⊗ ¬A ⇒ ⊥` (NC) trivially follow

it is strange that intuitionistic and dual intuitionistic logic both lose `⅋` and their dual implication connective. this can be avoided by breaking things down one more time, into basic type theory.
because we're looking at things from an intuitionistic perspective (only one term on the RHS of the sequent + negations), `⅋` is completely worthless (all of its rules end up getting phrased in terms of `⊗` and `¬`).
let's try to break down the rules for `→` and `←` in terms of `⅋` again.
* `A → B` becomes `¬ₙ A ⅋ B`; the constructor becomes `(λx.e) : 1 ⇒ ¬ₙA ⅋ B`; the eliminator becomes `A ⊗ ¬ₙA ⇒ ⊥` (i.e. NC).
* `A ← B` becomes `A ⅋ ¬ₓ B`; the constructor becomes `1 ⇒ A ⅋ ¬ₓA` (i.e. LEM); the eliminator becomes `(λ₂x.e) : ¬ₓA ⊗ B ⇒ ⊥`.
* `¬ₙA = A → ⊥`; it is a negation for which NC holds, but not LEM.; `¬ₓA = 1 ← A`; it is a negation for which LEM holds, but not NC.
* basic logic does not have negation anywhere in its rules, actually. the implications `←` and `→` really are fundamental.
  but if it did have negations, the negations would look something like this: `A ⊢ B` entails `A, ¬ₓB ⊢` and `⊢ ¬ₙA, B` and vice versa.

This allows us to explain precisely which connectives are values:
* `A ⊗ B` and `¬ₙ(A ⅋ B)` are structs; `¬ₓ(A ⊗ B)` and `A ⅋ B` are computations which return twice.
* `1` and `¬ₙ⊥` are empty structs; `¬ₓ1` and `⊥` are computations which do not return.
* `A ⊕ B` and `¬ₓ(A & B)` are tagged unions; `¬ₙ(A ⊕ B)` and `A & B` are pairs of computations.
* `0` and `¬ₓ⊤` are empty unions; `¬ₙ0` and `¬ₙ⊤` are computations which cannot be called.
* `¬(A → B)` is `A ⊗ ¬ₙB` and `A ← B` is `A ⊗ ¬ₓB`; `A → B` is `¬ₙA ⅋ B` and `A ← B` is `A ⅋ ¬ₓB`.

Observe that `¬ₓ` can return a variable number of times (because of LEM) and `¬ₙ` can be called a variable number of times (because of NC).
Also observe that values and their negative duals have *exactly the same representation*.

This is the source of the duality between intuitionistic TT and dual intuitionistic TT.

**END BUT NOT REALLY**: I provided additional context but didn't really explain much.

Part two later, maybe?

### Other somewhat related stuff.
My other gist is somewhat related: [Full Classical Linear Type Theory](https://gist.github.com/jamestmartin/160b70a5f8b7a3f2aa577111194fe3d0)

Also I made another conjecture about how the only primitive connective for classical linear type theory is `;` representing dependent synchronous messaging, but I posted it on April 1st so I think people thought it was a shitpost.

Also this one is a lot less thought-out and perhaps less likely to be correct.

All binary connectives can be unified into *one* connective. I call it "interaction" (or maybe "dependent junction"). Observe:
* `Π A B = A,1;1,B` where B depends on A
* `Σ A B = 1,A;1,B` where B depends on A
* `A & B = Π 2 F` where `F(⋆, false) = A` and `F(⋆, true) = B`
* `A ⊕ B = Σ 2 F` where `F(false, ⋆) = A` and `F(true, ⋆) = B`
* `A ⊗ B = Π I F` where `F(⋆, i0) = 1,A;1,B` and `F(⋆, i1) = 1,B;1,A` and `A` and `B` are constant
* `A ⅋ B = Σ I F` where `F(i0, ⋆) = 1,A;1,B` and `F(i1, ⋆) = 1,B;1,A` and `A` and `B` are constant
* `¬(A,B;C,D) = B,A;D,C` where C and D may depend on A and B

To construct `A,B;C,D` you construct an A, eliminate a B, construct a C, then eliminate a D. Dually, to eliminate it, you construct a B, eliminate an A, construct a D, then eliminate a C.
Operationally it represents two threads exchanging an A and a B and then exchanging a C and a D dependent on the previous exchange. Interactions may be (dependently) chained an arbitrary number of times to represent a typed (dependent) communication channel.
It arises quite naturally when trying to implement the system and is not as complicated as it may look.

(`I` is a bit magical. It blocks the stack, forcing you to only use completed transactions. Additionally, both sides must be heterogenously equal. In the case of `⊗` and `⅋`, `;` is commutative when derived from the empty stack.)

(NB: `I` is totally ad-hoc. It basically just represents "whatever the minimal constraints are for this to work". Any similarity to the interval type is coincidental.)
