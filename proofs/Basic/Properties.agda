{-# OPTIONS --with-K --injective-type-constructors #-}
module Basic.Properties where

open import Basic
open import Basic.Admissible
open import SqEq

import Data.Empty as E
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Function.Equality
open import Function.HalfAdjointEquivalence
open import Relation.Binary.HeterogeneousEquality as HetEq
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary

Visible : Context n → Set
Visible {n} Γ = ∃ λ τ → Γ ≅ ∅ ,, τ

-- Visibility follows syntactically from the operational rules.
visibility : Term Γ Δ → Visible Γ ⊎ Visible Δ
visibility (⊗L x) = inj₁ (_ , refl)
visibility (⅋R x) = inj₂ (_ , refl)
visibility (⅋L x x₁ x₂) = inj₁ (_ , refl)
visibility (⊗R x x₁ x₂) = inj₂ (_ , refl)
visibility (1L x) = inj₁ (_ , refl)
visibility (⊥R x) = inj₂ (_ , refl)
visibility ⊥L = inj₁ (_ , refl)
visibility 1R = inj₂ (_ , refl)
visibility (⊕L x x₁) = inj₁ (_ , refl)
visibility (&R x x₁) = inj₂ (_ , refl)
visibility (&L₁ x) = inj₁ (_ , refl)
visibility (&L₂ x) = inj₁ (_ , refl)
visibility (⊕R₁ x) = inj₂ (_ , refl)
visibility (⊕R₂ x) = inj₂ (_ , refl)
visibility 0L = inj₁ (_ , refl)
visibility ⊤R = inj₂ (_ , refl)
visibility (⇐L x) = inj₁ (_ , refl)
visibility (⇒R x) = inj₂ (_ , refl)
visibility (⇒L x x₁) = inj₁ (_ , refl)
visibility (⇐R x x₁) = inj₂ (_ , refl)
visibility (⇐U x x₁) = inj₁ (_ , refl)
visibility (⇒U x x₁) = inj₂ (_ , refl)

dual : Type → Type
dual (τ ⊗ τ₁) = dual τ ⅋ dual τ₁
dual (τ ⊕ τ₁) = dual τ & dual τ₁
dual (τ & τ₁) = dual τ ⊕ dual τ₁
dual (τ ⅋ τ₁) = dual τ ⊗ dual τ₁
dual (τ ⇒ τ₁) = dual τ₁ ⇐ dual τ
dual (τ ⇐ τ₁) = dual τ₁ ⇒ dual τ
dual ⊤ = 0'
dual ⊥ = 1'
dual 0' = ⊤
dual 1' = ⊥

dualCtx : Context n → Context n
dualCtx ∅ = ∅
dualCtx (Γ ,, x) = dualCtx Γ ,, dual x

symmetricExch : Exch Γ Γ₁ Γ₂ → Exch (dualCtx Γ) (dualCtx Γ₁) (dualCtx Γ₂)
symmetricExch done = done
symmetricExch (left exch) = left (symmetricExch exch)
symmetricExch (right exch) = right (symmetricExch exch)

symmetry : Term Γ Δ → Term (dualCtx Δ) (dualCtx Γ)
symmetry (⊗L x) = ⅋R (symmetry x)
symmetry (⅋R x) = ⊗L (symmetry x)
symmetry (⅋L x x₁ x₂) = ⊗R (symmetricExch x) (symmetry x₁) (symmetry x₂)
symmetry (⊗R x x₁ x₂) = ⅋L (symmetricExch x) (symmetry x₁) (symmetry x₂)
symmetry (1L x) = ⊥R (symmetry x)
symmetry (⊥R x) = 1L (symmetry x)
symmetry ⊥L = 1R
symmetry 1R = ⊥L
symmetry (⊕L x x₁) = &R (symmetry x) (symmetry x₁)
symmetry (&R x x₁) = ⊕L (symmetry x) (symmetry x₁)
symmetry (&L₁ x) = ⊕R₁ (symmetry x)
symmetry (&L₂ x) = ⊕R₂ (symmetry x)
symmetry (⊕R₁ x) = &L₁ (symmetry x)
symmetry (⊕R₂ x) = &L₂ (symmetry x)
symmetry 0L = ⊤R
symmetry ⊤R = 0L
symmetry (⇐L x) = ⇒R (symmetry x)
symmetry (⇒R x) = ⇐L (symmetry x)
symmetry (⇒L x x₁) = ⇐R (symmetry x₁) (symmetry x)
symmetry (⇐R x x₁) = ⇒L (symmetry x₁) (symmetry x)
symmetry (⇐U x x₁) = ⇒U (symmetry x₁) (symmetry x)
symmetry (⇒U x x₁) = ⇐U (symmetry x₁) (symmetry x)

reflect⊗₁ : ∀ {A B} → (∅ ,, A ⊗ B ⊢ Δ) → (∅ ,, A ,, B ⊢ Δ)
reflect⊗₁ x = cutL (⊗R (right (left done)) identity identity) x

{-
reflect⊗₁ (⊗L x) = x
reflect⊗₁ (⅋R (⊗L ()))
reflect⊗₁ (⊗R (left done) x₁ x₂) = ⊗R (left (left done)) (reflect⊗₁ x₁) x₂
reflect⊗₁ (⊗R (right done) x₁ x₂) = ⊗R (right (right done)) x₁ (reflect⊗₁ x₂)
reflect⊗₁ (⊥R (⊗L ()))
reflect⊗₁ (&R x x₁) = &R (reflect⊗₁ x) (reflect⊗₁ x₁)
reflect⊗₁ (⊕R₁ x) = ⊕R₁ (reflect⊗₁ x)
reflect⊗₁ (⊕R₂ x) = ⊕R₂ (reflect⊗₁ x)
reflect⊗₁ ⊤R = ⊤R
reflect⊗₁ (⇐R x x₁) = ⇐R (reflect⊗₁ x) x₁
-}

reflect⊗₂ : ∀ {A B} → (∅ ,, A ,, B ⊢ Δ) → (∅ ,, A ⊗ B ⊢ Δ)
reflect⊗₂ x = ⊗L x
-- Partially composed with cut to always produce canonical form.
{-
reflect⊗₂ x@(⊗R (left (right done)) x₁ x₂) = ⊗L x
reflect⊗₂ x@(⊗R (right (left done)) x₁ x₂) = ⊗L x
reflect⊗₂ (⊗R (left (left done)) x₁ x₂) = ⊗R (left done) (reflect⊗₂ x₁) x₂
reflect⊗₂ (⊗R (right (right done)) x₁ x₂) = ⊗R (right done) x₁ (reflect⊗₂ x₂)
reflect⊗₂ (&R x x₁) = &R (reflect⊗₂ x) (reflect⊗₂ x₁)
reflect⊗₂ (⊕R₁ x) = ⊕R₁ (reflect⊗₂ x)
reflect⊗₂ (⊕R₂ x) = ⊕R₂ (reflect⊗₂ x)
reflect⊗₂ ⊤R = ⊤R
reflect⊗₂ (⇐R x x₁) = ⇐R (reflect⊗₂ x) x₁
-}

-- Counterexample to the inequivalence of 
reflect⊗-inj-cx₁ : ∀ {A B} → (x : ∅ ,, A ,, B ⊢ ∅ ,, ⊤) → x ≡ ⊤R
reflect⊗-inj-cx₁ ⊤R = refl

reflect⊗-inj-cx : ∀ {A B} → ¬ ∃ λ (x : ∅ ,, A ⊗ B ⊢ ∅ ,, ⊤) → ∀ (x' : ∅ ,, A ⊗ B ⊢ ∅ ,, ⊤) → x ≡ x'
reflect⊗-inj-cx (⊗L ⊤R , snd) with snd ⊤R
... | ()
reflect⊗-inj-cx (⊤R , snd) with snd (⊗L ⊤R)
... | ()

-- TODO: Use the counterexample to refute that reflect⊗ can be an equivalence.
{-
reflect⊗-inequiv : ∀ {A B} → ¬ ∀ {n} {Δ : Context n} → (∅ ,, A ⊗ B ⊢ Δ) ≃ (∅ ,, A ,, B ⊢ Δ)
reflect⊗-inequiv eqvs with eqvs {Δ = ∅ ,, ⊤}
... | eqv with _≃_.
-}

reflect1₁ : ∅ ,, 1' ⊢ Δ → ∅ ⊢ Δ
reflect1₁ (⅋R (1L ()))
reflect1₁ (⊗R (left done) x₁ x₂) = ⊗R done (reflect1₁ x₁) x₂
reflect1₁ (⊗R (right done) x₁ x₂) = ⊗R done x₁ (reflect1₁ x₂)
reflect1₁ (1L x) = x
reflect1₁ (⊥R x) = ⊥R (reflect1₁ x)
reflect1₁ (&R x x₁) = &R (reflect1₁ x) (reflect1₁ x₁)
reflect1₁ (⊕R₁ x) = ⊕R₁ (reflect1₁ x)
reflect1₁ (⊕R₂ x) = ⊕R₂ (reflect1₁ x)
reflect1₁ ⊤R = ⊤R
reflect1₁ (⇐R x x₁) = ⇐R (reflect1₁ x) x₁

reflect1₂ : ∅ ⊢ Δ → ∅ ,, 1' ⊢ Δ
reflect1₂ = 1L

reflect&₁ : ∀ {A B} → (Γ ⊢ ∅ ,, A & B) → (Γ ⊢ ∅ ,, A × Γ ⊢ ∅ ,, B)
reflect&₁ (⊗L (&R x x₁)) = ⊗L x , ⊗L x₁
reflect&₁ (⅋L (left done) x₁ x₂) = (⅋L (left done) (cut x₁ (&L₁ identity)) x₂) , ⅋L (left done) (cut x₁ (&L₂ identity)) x₂
reflect&₁ (⅋L (right done) x₁ x₂) = (⅋L (right done) x₁ (cut x₂ (&L₁ identity))) , ⅋L (right done) x₁ (cut x₂ (&L₂ identity))
reflect&₁ (1L (&R x x₁)) = 1L x , 1L x₁
reflect&₁ (⊕L x x₁) = ⊕L (cut x (&L₁ identity)) (cut x₁ (&L₁ identity)) , ⊕L (cut x (&L₂ identity)) (cut x₁ (&L₂ identity))
reflect&₁ (&R x x₁) = x , x₁
reflect&₁ (&L₁ x) = cut (&L₁ identity) (proj₁ (reflect&₁ x)) , cut (&L₁ identity) (proj₂ (reflect&₁ x))
reflect&₁ (&L₂ x) = cut (&L₂ identity) (proj₁ (reflect&₁ x)) , cut (&L₂ identity) (proj₂ (reflect&₁ x))
reflect&₁ 0L = 0L , 0L
reflect&₁ (⇒L x x₁) = (⇒L x (cut x₁ (&L₁ identity))) , (⇒L x (cut x₁ (&L₂ identity)))

reflect&₂ : ∀ {A B} → (Γ ⊢ ∅ ,, A × Γ ⊢ ∅ ,, B) → (Γ ⊢ ∅ ,, A & B)
reflect&₂ (x , y) = &R x y

-- NO multiplicative EM is provable, nor indeed any such ⅋ at all.
ems-unprovable : ∀ {A B} → ¬ Term ∅ (∅ ,, A ⅋ B)
ems-unprovable (⅋R ())

-- It makes no (*logical*) difference if you follow from ∅ or 1.
ems-unprovable₂ : ∀ {A B} → ¬ Term (∅ ,, 1') (∅ ,, A ⅋ B)
ems-unprovable₂ (⅋R (1L ()))
ems-unprovable₂ (1L (⅋R ()))

-- TODO: Reflection for ⊤.
ems-unprovable₃ : ∀ {A B} → ¬ Term (∅ ,, ⊤) (∅ ,, A ⅋ B)
ems-unprovable₃ (⅋R ())

-- The rest of the EM′s appear to follow obviously.
ems-unprovable₄ : ∀ {A B} → ¬ Term (∅ ,, (A ⅋ B) ⇒ ⊥) ∅
ems-unprovable₄ (⇒L p p₁) = ems-unprovable p

-- Whereas *no* instance of multiplicative EM is valid,
-- there are valid instances of additive EM (for anything that's provable),
-- but additive EMs have counterexamples in things which *aren't* provable.
-- I uniformly use `⊥ ⊗ ⊥` as a counterexample because it has no proofs nor refutations.
em-unprovable₄ : ¬ ∀ A → Term ∅ (∅ ,, A ⊕ (A ⇒ ⊥))
em-unprovable₄ em with em (⊥ ⊗ ⊥)
... | ⊕R₁ (⊗R done (⊥R ()) p₁)
... | ⊕R₂ (⇒R (⊗L (⊥R ())))
... | ⊕R₂ (⇒R (⊥R (⊗L ())))

em-unprovable₅ : ¬ ∀ A → Term ∅ (∅ ,, A ⊕ (⊤ ⇐ A))
em-unprovable₅ em with em (⊥ ⊗ ⊥)
... | ⊕R₁ (⊗R done (⊥R ()) p₁)
... | ⊕R₂ (⇐R p (⊗L ()))

em-unprovable₆ : ¬ ∀ A → Term (∅ ,, (A ⊕ (A ⇒ ⊥)) ⇒ ⊥) (∅ ,, ⊥)
-- This would be smaller if I chose a better counterexample,
-- but we don't care about specific choice of counterexample
-- and just mindlessly smashing out the refutation is easier than coming up with one.
em-unprovable₆ em with em (⊥ ⊗ ⊥)
... | ⊥R (⇒L (⊕R₁ (⊗R done (⊥R ()) p₁)) ⊥L)
... | ⊥R (⇒L (⊕R₂ (⇒R (⊗L (⊥R ())))) ⊥L)
... | ⊥R (⇒L (⊕R₂ (⇒R (⊥R (⊗L ())))) ⊥L)
... | ⇒L (⊕R₁ (⊗R done (⊥R ()) p₂)) p₁
... | ⇒L (⊕R₂ (⇒R (⊗L (⊥R ())))) p₁
... | ⇒L (⊕R₂ (⇒R (⊥R (⊗L ())))) p₁

em-unprovable₇ : ¬ ∀ A → Term ∅ (∅ ,, A ⊕ (1' ⇐ A))
em-unprovable₇ em with em (⊥ ⊗ ⊥)
... | ⊕R₁ (⊗R done (⊥R ()) p₁)
... | ⊕R₂ (⇐R p (⊗L ()))

em-provable₇ : ¬ ∀ A → Term ∅ (∅ ,, A ⊕ (1' ⇐ A))
em-provable₇ em with em (⊥ ⊗ ⊥)
... | ⊕R₁ (⊗R done (⊥R ()) p₁)
... | ⊕R₂ (⇐R p (⊗L ()))

em-unprovable₈ : ¬ ∀ A → Term ∅ (∅ ,, A ⊕ (A ⇒ 0'))
em-unprovable₈ em with em (⊥ ⊗ ⊥)
... | ⊕R₁ (⊗R done (⊥R ()) p₁)
... | ⊕R₂ (⇒R (⊗L ()))
