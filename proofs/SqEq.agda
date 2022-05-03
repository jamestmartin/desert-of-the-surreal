-- NB: --with-K isn't necessary for this module, see https://github.com/agda/agda/issues/5816
{-# OPTIONS --safe --with-K #-}
-- | Squashed (definitionally proof-irrelevant) propositional equality.
-- This is much nicer than `.(A ≡ B)` because `.irrAx : .A → A` does not hold
-- whereas the equivalent for Prop does. This makes proving things like
-- injectivity of constructors vastly easier.
--
-- Okay, but why do we care about squashed propositional equality at all?
-- So that we can write coercion functions `x ≡ y → F x → F y` which
-- compute definitionally on their arguments. `subst` doesn't for whatever reason,
-- even with UIP, which is *extremely* annoying and prevents your functions
-- from computing on open terms, which makes proofs *very* difficult.
module SqEq where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

infix 5 _≐_
data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl' : x ≐ x

-- squash equality
sq-eq : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≐ y
sq-eq refl = refl'

-- successor is an injective function
suc-inj-irr : ∀ {n₁ n₂ : ℕ} → ℕ.suc n₁ ≐ suc n₂ → n₁ ≐ n₂
suc-inj-irr refl' = refl'

-- squashed equalities are transitive
trans-irr : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ x₃ : A} → x₁ ≐ x₂ → x₁ ≐ x₃ → x₂ ≐ x₃
trans-irr refl' refl' = refl'

-- squashed equalities are congruent
cong-irr : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x₁ x₂} → x₁ ≐ x₂ → f x₁ ≐ f x₂
cong-irr _ refl' = refl'
