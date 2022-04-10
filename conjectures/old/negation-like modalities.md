# Negation-like modalities

most of this is repeating stuff that we've said before, but I'm going to restate the original 3 conjectures in a way which includes some of our new knowledge and which focuses more on the logic PoV.

## The conjectures

1. more-or-less that entire family of logics (including e.g. LDJ and basic) correspond with well-behaved type theories

   1.1. these families of logics form a lattice (if this is not true like you said, the rest of what I say here may still hold)

   1.2. many of these logics have not been studied as type theories before

2. we can define the features/properties which characterize these logics/type theories, and they correspond with the semantics of the type theory as a programming language

   2.1. there is an interaction between structural rules and left/right contexts in determining which logics will be degenerate

   2.2. implication and exclusion interact with left/right contexts in a more sophisticated way than other connectives

3. we can determine which combinations of features/properties are valid and which are degenerate based on how those properties interact

   3.1. logics/type theories become degenerate if they have the wrong set of features, and can degenerate in multiple ways
   3.1.1. higher-order logics/dependent type theories may degenerate to equationally-deficient logics/type theories which are often/usually first-order (and I have a few examples in type theory)

   3.1.2. constructive logics/type theories may degenerated to non-constructive logics/type theories (and I have a few examples in type theory)
   3.1.2.1. non-constructive logics can be embedded in non-degenerate logics using an appropriate negation-like modality (and several of them are already known to type theorists) (see also: [Why does it matter if canonicity holds for irrelevant types?](https://proofassistants.stackexchange.com/q/965/788), [How does Prop relate to h-prop and double negation?](https://proofassistants.stackexchange.com/q/1153/788) (I never got an answer but I suspect this system of modalities is the answer.))

   3.1.3. logics/type theories may not degenerate at all

4. non-degenerate theories have negation-like modalities which may be characterized by a few properties, such as

   4.1. classicality/(dual) intuitionism/basicness (which corresponds with sides of the context?)

   4.2. structural/substructural/non-structural (specific choice of structural rules dependent on choice of context)

   4.3. paraconsistent/paracomplete/both (but whether this is weak/strong para-whateverness is dependent on the choice of context?)

   4.4. truth-preserving/false-preserving/degree-preserving(?) (whether they embed stronger theories or how the embedded theories are stronger; e.g. intuitionistic double-negation is truth-preserving because `A → ¬¬A` but `A ↛ ¬¬A` because LEM holds under double negation)

   4.5. the relationship between left/right context and structural rules translates into the semantics of the resulting type theory in terms of how it preserves duality, polarity, and relationships between data and code (which typically corresponds with polarity in intuitionistic type theory, but this does not have to be the case)

## The examples & meaning
to partially answer your question about what type theories exist, here are some specific examples of type theories in this realm (not trying to categorize them in terms of your negation lattice conjecture for now):
* [𝜆𝜇-calculus](https://proofassistants.stackexchange.com/q/541/788) is a FOL-degenerate system corresponding with a classical structural first-order logic
* there may be an equationally-deficient system corresponding with a higher-order logic but with really nasty semantics, perhaps including no meaningful identity type at all (similar to GHC Haskell) (presumably this is related to the fire triangle/call-by-push-value?)
* MLTT or CIC with LEM as an axiom is a nonconstructively-degenerate system corresponding with a classical structural higher-order logic
* MLTT is a non-degenerate system corresponding with an intuitionistic structural higher-order logic
* Agda and Coq contain Prop and SProp, which I conjecture to be a paraconsistent and paracomplete structural dual-context degree-preserving negation-like modality (or something like that?)
* my incomplete classical linear type theory which I conjectured 10 days ago may correspond with a classical non-structural higher-order logic
* in my original post I conjecture a specific system corresponding with dual intuitionistic structural higher-order logic (related to LDJ?) and another one corresponding with basic non-structural higher-order logic
* I also conjecture specific substructural systems which lie somewhere in the confusing intermediate space which we've conjectured
* I also conjecture that "all the other" (non-degenerate?) systems exist

equational deficiency is the result of all types being "code" and not "data" and theories with more "data" are equationally better. equationality is tied to type-theoretic eta rules. equations may be either definitional or propositional; equations for implication are usually propositional or may not exist; equations for other connectives may be definitional or propositional or not exist; equations for the units are tied to typed conversion which I only partially understand and which might not be relevant?

the relationship between structural rules and left/right-contexts are probably tied to the laws required for equivalences between connectives. conjunction and implication are tied to left contexts; disjunction and exclusion are tied to right contexts; weakening is tied to the relationship between implication and disjunction in a left-handed system; further connections certainly exist but I am unsure of them.

implication and exclusion are related to "par" and "times" in terms of specific negations (in particular paracomplete/paraconsistent negations respectively); their rules embed entailment in a specific way via the constructor/eliminator `λ`, in a way which I expect to have important implications.

## Other stuff
Copy/pasting some of my own messages for later. Not copying Paraconsista's for now, but I need to later.

it's known that cut elimination corresponds with strong normalization (or something like that), and call-by-value and call-by-name are dual. perhaps this is related to left cut (CBV)/right cut (CBN). based on messing with basic type theory previously (even though I haven't worked on that for a while), when implementing `cutL`/`cutR` I noticed that they are mutually recursive, using `cutL` to substitute in positive types and `cutR` to substitute in negative types, which would correspond with the expected evaluation strategies for positive/negative types as well.

not sure how the weaker cut and full cut factor into this. full cut seems suspect and may correspond with some form of non-determinism (1.1/1.2?). also not sure how different identity types factor into this.
also not sure about the precise relationship between cuts and evaluation because I don't believe cut alone is sufficient to implement evaluation (and thus correspond with evaluation strategies), even if the polarity distinction is there.

## More information in need of a rewrite

this is a follow up to/partial rewrite of [Big conjectures Part 1](https://gist.github.com/jamestmartin/ef323649a6a388be939b8ee5a596cfed). I include more information on code vs. data, eta, and the relationship between context-handedness and structural rules there, although those parts are in dire need of a rewrite. I am copy/pasting (with minor adjustments) those parts here.

### Relationship between eta laws, context-handedness, structural laws, and equivalences between connectives

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

### Really really old stuff on meaning of data/code symmetry
s I mentioned before, in intuitionistic type theory, `¬` and `Id ¬` are trivial. It doesn't have to be this way; I'll explain in terms of data, computations, and triviality.

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

### Really really old cross-references
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

## Quick clarifications
All of these are old messages which need to be updated and incorporated into the main draft.

### Duality vs. Polarity
if duality is the symmetry between
* ⊕ and &
* ⊗ and ⅋
* 0 and ⊤
* A and ¬A

then polarity is the symmetry across (+/-)
* ⊗ and &
* ⊕ and ⅋
* 0 and ⊥
* A and ¬A

(¬A usually has both opposite duality and opposite polarity to A, but this need not be the case.)

for example:
* classical logic has full duality (∧ / ∨) and self-polarity (⊕ = ∨ = ⅋)
* (dual) intuitionistic logic has partial (internal) duality (⊕ and &, but no proper dual to →) and non-trivial polarity (⊗ = & but ⊕ ≠ →, no ⅋ or ←)
* basic logic has full duality and full polarity

more generally:
* classical logics (resp. basic logics) may have polarity, but both poles correspond to computation (resp. data)
* intuitionistic logics (resp. dual intuitionistic logics) have polarity but not complete symmetry, and positive (resp. negative) types are data whereas negative (resp. positive) types are computation 

In (dual) intuitionistic logic, polarity corresponds with data/code (or value/computation) symmetry, but this breaks down in other logics (e.g. classical logic is "all code"?)

### The trivial result
I'd like to clarify that (trivial, but important) result:
* in intuitionistic-polarity type theory, mutual implication between conjunctions requires both weakening and contraction
* in intuitionistic-polarity type theory, mutual implication between *⊕ and →* requires weakening, (trivially, NC,) and LEM but not *contraction*
* I would conjecture dual results for dual intuitionistic-parity type theory
* `→` is not necessarily the same as *true* negative disjunction, `⅋`, nor the *other* negative disjunction,  exclusion (`←`). I don't know what it would mean to include `⅋` or `←` yet, but if you did, I would expect mutual implication between them to use different sets of rules (resp. both structural rules, contraction?) and dual rules for dual intuitionistic TT
