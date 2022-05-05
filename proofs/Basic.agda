{-# OPTIONS --with-K --injective-type-constructors #-}
module Basic where

open import SqEq

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.HeterogeneousEquality as HetEq
open import Relation.Binary.PropositionalEquality as PropEq

variable n n₁ n₂ n₃ n₄ n₅ n₆ : ℕ

data Type : Set where
  _⊗_ _⊕_ _&_ _⅋_ _⇒_ _⇐_ : Type → Type → Type
  ⊤ ⊥ 0' 1' : Type
infix 16 _⇒_ _⇐_
infix 15 _⊕_ _⅋_
infix 14 _⊗_ _&_

variable τ τ₁ τ₂ τ₃ τ₄ : Type

data Context : ℕ → Set where
  ∅ : Context 0
  _,,_ : Context n → Type → Context (suc n)
infixl 10 _,,_ _++_

variable Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : Context n

-- Coercion function which computes on its constructors.
ctx-coe : n₁ ≐ n₂ → Context n₁ → Context n₂
ctx-coe {.0} {zero} _ ∅ = ∅
ctx-coe {.(suc _)} {suc n₂} p (Γ ,, x) = ctx-coe (suc-inj-irr p) Γ ,, x

-- Append contexts.
_++_ : Context n₁ → Context n₂ → Context (n₂ + n₁)
Γ₁ ++ ∅ = Γ₁
Γ₁ ++ (Γ₂ ,, x) = (Γ₁ ++ Γ₂) ,, x

-- Left identity for appending contexts.
++-id : ∅ ++ Γ ≅ Γ
++-id {Γ = ∅} = refl
++-id {suc n} {Γ = Γ ,, x} = HetEq.icong Context (+-identityʳ n) (_,, x) (++-id {Γ = Γ})

-- | Choose which variables to send down the left side of the term,,
-- and which to send down the right side of the term.
-- By iterating this at every multiplicative junction,
-- the rule of exchange becomes admissible without needing to clutter
-- with explicit exchange nodes or redundant information.
data Exch : (Γ : Context n) → (Γ₁ : Context n₁) → (Γ₂ : Context n₂) → Set where
  done : Exch ∅ ∅ ∅
  -- Send a variable in the context to the left (resp. right) sub-term.
  left : Exch Γ Γ₁ Γ₂ → Exch (Γ ,, τ) (Γ₁ ,, τ) Γ₂
  right : Exch Γ Γ₁ Γ₂ → Exch (Γ ,, τ) Γ₁ (Γ₂ ,, τ)

-- TODO: write actual coercion functions so it doesn't have to match on Γ₂
-- or so that I can do other coercions if necessary.
exch-coe₁ : Exch Γ Γ₁ (∅ ++ Γ₂) → Exch Γ Γ₁ Γ₂
exch-coe₁ {Γ₂ = ∅} p = p
exch-coe₁ {Γ₂ = Γ₂ ,, x} (left p) = left (exch-coe₁ p)
exch-coe₁ {Γ₂ = Γ₂ ,, x} (right p) = right (exch-coe₁ p)

exch-coe₂ : Exch Γ (∅ ++ Γ₁) Γ₂ → Exch Γ Γ₁ Γ₂
exch-coe₂ {Γ₁ = ∅} p = p
exch-coe₂ {Γ₁ = Γ₁ ,, x} (left p) = left (exch-coe₂ p)
exch-coe₂ {Γ₁ = Γ₁ ,, x} (right p) = right (exch-coe₂ p)

-- The left sub-term uses the rest of the context.
lefts : Exch Γ Γ₁ Γ₂ → Exch (Γ ++ Δ) (Γ₁ ++ Δ) Γ₂
lefts {Δ = ∅} x = x
lefts {Δ = _ ,, _} x = left (lefts x)

-- The left sub-term uses the *entire* context.
all-lefts : Exch Γ Γ ∅
all-lefts {Γ = ∅} = done
all-lefts {Γ = _ ,, _} = left all-lefts

rights : Exch Γ Γ₁ Γ₂ → Exch (Γ ++ Δ) Γ₁ (Γ₂ ++ Δ)
rights {Δ = ∅} x = x
rights {Δ = _ ,, _} x = right (rights x)

all-rights : Exch Γ ∅ Γ
all-rights {Γ = ∅} = done
all-rights {Γ = _ ,, _} = right all-rights

-- Swap the contexts used by the left and right sub-terms.
reverse-exch : Exch Γ Γ₁ Γ₂ → Exch Γ Γ₂ Γ₁
reverse-exch done = done
reverse-exch (left p) = right (reverse-exch p)
reverse-exch (right p) = left (reverse-exch p)

-- Append two sets of exchanges.
over : Exch Γ Γ₁ Γ₂ → Exch Δ Δ₁ Δ₂ → Exch (Δ ++ Γ) (Δ₁ ++ Γ₁) (Δ₂ ++ Γ₂)
over done q = q
over (left p) q = left (over p q)
over (right p) q = right (over p q)

data Term : (Γ : Context n₁) → (Δ : Context n₂) → Set where
  -- Identity axiom.
  var : Term (∅ ,, τ) (∅ ,, τ)

  -- Operational rules for multiplicatives.
  ⊗L : Term (∅ ,, τ₁ ,, τ₂) Δ → Term (∅ ,, τ₁ ⊗ τ₂) Δ
  ⅋R : Term Γ (∅ ,, τ₁ ,, τ₂) → Term Γ (∅ ,, τ₁ ⅋ τ₂)
  ⅋L : Exch Δ Δ₁ Δ₂ → Term (∅ ,, τ₁) Δ₁ → Term (∅ ,, τ₂) Δ₂ → Term (∅ ,, τ₁ ⅋ τ₂) Δ
  ⊗R : Exch Γ Γ₁ Γ₂ → Term Γ₁ (∅ ,, τ₁) → Term Γ₂ (∅ ,, τ₂) → Term Γ (∅ ,, τ₁ ⊗ τ₂)
  1L : Term ∅ Δ → Term (∅ ,, 1') Δ
  ⊥R : Term Γ ∅ → Term Γ (∅ ,, ⊥)
  ⊥L : Term (∅ ,, ⊥) ∅
  1R : Term ∅ (∅ ,, 1')

  -- Operational rules for additives.
  ⊕L : Term (∅ ,, τ₁) Δ → Term (∅ ,, τ₂) Δ → Term (∅ ,, τ₁ ⊕ τ₂) Δ
  &R : Term Γ (∅ ,, τ₁) → Term Γ (∅ ,, τ₂) → Term Γ (∅ ,, τ₁ & τ₂)
  &L₁ : Term (∅ ,, τ₁) Δ → Term (∅ ,, τ₁ & τ₂) Δ
  &L₂ : Term (∅ ,, τ₂) Δ → Term (∅ ,, τ₁ & τ₂) Δ
  ⊕R₁ : Term Γ (∅ ,, τ₁) → Term Γ (∅ ,, τ₁ ⊕ τ₂)
  ⊕R₂ : Term Γ (∅ ,, τ₂) → Term Γ (∅ ,, τ₁ ⊕ τ₂)
  0L : Term (∅ ,, 0') Δ
  ⊤R : Term Γ (∅ ,, ⊤)

  -- Operational rules for implications.
  ⇐L : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term (∅ ,, τ₁ ⇐ τ₂) ∅
  ⇒R : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term ∅ (∅ ,, τ₁ ⇒ τ₂)
  ⇒L : Term ∅ (∅ ,, τ₁) → Term (∅ ,, τ₂) Δ → Term (∅ ,, τ₁ ⇒ τ₂) Δ
  ⇐R : Term Γ (∅ ,, τ₁) → Term (∅ ,, τ₂) ∅ → Term Γ (∅ ,, τ₁ ⇐ τ₂)
  ⇐U : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term (∅ ,, τ₃) (∅ ,, τ₄) → Term (∅ ,, τ₁ ⇐ τ₄) (∅ ,, τ₂ ⇐ τ₃)
  ⇒U : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term (∅ ,, τ₃) (∅ ,, τ₄) → Term (∅ ,, τ₂ ⇒ τ₃) (∅ ,, τ₁ ⇒ τ₄)

  -- Exchange and cut are admissible.

_⊢_ : (Γ : Context n₁) → (Δ : Context n₂) → Set
_⊢_ = Term
infix 5 _⊢_
