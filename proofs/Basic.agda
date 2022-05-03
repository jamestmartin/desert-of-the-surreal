{-# OPTIONS --with-K --injective-type-constructors #-}
module Basic where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.HeterogeneousEquality as HetEq
open import Relation.Binary.PropositionalEquality as PropEq

private variable n n₁ n₂ n₃ n₄ n₅ n₆ : ℕ

infix 5 _≐_
data _≐_ {ℓ} {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl' : x ≐ x

sq-eq : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≐ y
sq-eq refl = refl'

suc-inj-irr : ∀ {n₁ n₂ : ℕ} → ℕ.suc n₁ ≐ suc n₂ → n₁ ≐ n₂
suc-inj-irr refl' = refl'

trans-irr : ∀ {ℓ} {A : Set ℓ} {x₁ x₂ x₃ : A} → x₁ ≐ x₂ → x₁ ≐ x₃ → x₂ ≐ x₃
trans-irr refl' refl' = refl'

cong-irr : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x₁ x₂} → x₁ ≐ x₂ → f x₁ ≐ f x₂
cong-irr _ refl' = refl'

data Type : Set where
  _⊗_ _⊕_ _&_ _⅋_ _⇒_ _⇐_ : Type → Type → Type
  ⊤ ⊥ 0' 1' : Type
infix 16 _⇒_ _⇐_
infix 15 _⊕_ _⅋_
infix 14 _⊗_ _&_

private variable τ τ₁ τ₂ τ₃ τ₄ : Type

data Context : ℕ → Set where
  ∅ : Context 0
  _,,_ : Context n → Type → Context (suc n)
infixl 10 _,,_ _++_

private variable Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : Context n

ctx-coe : n₁ ≐ n₂ → Context n₁ → Context n₂
ctx-coe {.0} {zero} _ ∅ = ∅
ctx-coe {.(suc _)} {suc n₂} p (Γ ,, x) = ctx-coe (suc-inj-irr p) Γ ,, x

_++_ : Context n₁ → Context n₂ → Context (n₂ + n₁)
Γ₁ ++ ∅ = Γ₁
Γ₁ ++ (Γ₂ ,, x) = (Γ₁ ++ Γ₂) ,, x

++-id : ∅ ++ Γ ≅ Γ
++-id {Γ = ∅} = refl
++-id {suc n} {Γ = Γ ,, x} = HetEq.icong Context (+-identityʳ n) (_,, x) (++-id {Γ = Γ})

reverse : Context n → Context n
reverse ∅ = ∅
reverse {suc n} (Γ ,, x) = ctx-coe (sq-eq (+-comm n 1)) (∅ ,, x ++ reverse Γ)

-- | Choose which variables to send down the left side of the term,,
-- and which to send down the right side of the term.
-- By iterating this at every multiplicative junction,,
-- we get the rule of exchange.
data Exch : (Γ : Context n) → (Γ₁ : Context n₁) → (Γ₂ : Context n₂) → Set where
  done : Exch ∅ ∅ ∅
  left : Exch Γ Γ₁ Γ₂ → Exch (Γ ,, τ) (Γ₁ ,, τ) Γ₂
  right : Exch Γ Γ₁ Γ₂ → Exch (Γ ,, τ) Γ₁ (Γ₂ ,, τ)

lefts : Exch Γ Γ₁ Γ₂ → Exch (Γ ++ Δ) (Γ₁ ++ Δ) Γ₂
lefts {Δ = ∅} x = x
lefts {Δ = _ ,, _} x = left (lefts x)

all-lefts : Exch Γ Γ ∅
all-lefts {Γ = ∅} = done
all-lefts {Γ = _ ,, _} = left all-lefts

rights : Exch Γ Γ₁ Γ₂ → Exch (Γ ++ Δ) Γ₁ (Γ₂ ++ Δ)
rights {Δ = ∅} x = x
rights {Δ = _ ,, _} x = right (rights x)

all-rights : Exch Γ ∅ Γ
all-rights {Γ = ∅} = done
all-rights {Γ = _ ,, _} = right all-rights

reverse-exch : Exch Γ Γ₁ Γ₂ → Exch Γ Γ₂ Γ₁
reverse-exch done = done
reverse-exch (left p) = right (reverse-exch p)
reverse-exch (right p) = left (reverse-exch p)

over : Exch Γ Γ₁ Γ₂ → Exch Δ Δ₁ Δ₂ → Exch (Δ ++ Γ) (Δ₁ ++ Γ₁) (Δ₂ ++ Γ₂)
over done q = q
over (left p) q = left (over p q)
over (right p) q = right (over p q)

data Term : (Γ : Context n₁) → (Δ : Context n₂) → Set where
  var : Term (∅ ,, τ) (∅ ,, τ)

  ⊗L : Term (∅ ,, τ₁ ,, τ₂) Δ → Term (∅ ,, τ₁ ⊗ τ₂) Δ
  ⅋R : Term Γ (∅ ,, τ₁ ,, τ₂) → Term Γ (∅ ,, τ₁ ⅋ τ₂)
  ⅋L : Exch Δ Δ₁ Δ₂ → Term (∅ ,, τ₁) Δ₁ → Term (∅ ,, τ₂) Δ₂ → Term (∅ ,, τ₁ ⅋ τ₂) Δ
  ⊗R : Exch Γ Γ₁ Γ₂ → Term Γ₁ (∅ ,, τ₁) → Term Γ₂ (∅ ,, τ₂) → Term Γ (∅ ,, τ₁ ⊗ τ₂)
  1L : Term ∅ Δ → Term (∅ ,, 1') Δ
  ⊥R : Term Γ ∅ → Term Γ (∅ ,, ⊥)
  ⊥L : Term (∅ ,, ⊥) ∅
  1R : Term ∅ (∅ ,, 1')

  ⊕L : Term (∅ ,, τ₁) Δ → Term (∅ ,, τ₂) Δ → Term (∅ ,, τ₁ ⊕ τ₂) Δ
  &R : Term Γ (∅ ,, τ₁) → Term Γ (∅ ,, τ₂) → Term Γ (∅ ,, τ₁ & τ₂)
  &L₁ : Term (∅ ,, τ₁) Δ → Term (∅ ,, τ₁ & τ₂) Δ
  &L₂ : Term (∅ ,, τ₂) Δ → Term (∅ ,, τ₁ & τ₂) Δ
  ⊕R₁ : Term Γ (∅ ,, τ₁) → Term Γ (∅ ,, τ₁ ⊕ τ₂)
  ⊕R₂ : Term Γ (∅ ,, τ₂) → Term Γ (∅ ,, τ₁ ⊕ τ₂)
  0L : Term (∅ ,, 0') Δ
  ⊤R : Term Γ (∅ ,, ⊤)

  ⇐L : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term (∅ ,, τ₁ ⇐ τ₂) ∅
  ⇒R : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term ∅ (∅ ,, τ₁ ⇒ τ₂)
  ⇒L : Term ∅ (∅ ,, τ₁) → Term (∅ ,, τ₂) Δ → Term (∅ ,, τ₁ ⇒ τ₂) Δ
  ⇐R : Term Γ (∅ ,, τ₁) → Term (∅ ,, τ₂) ∅ → Term Γ (∅ ,, τ₁ ⇐ τ₂)
  ⇐U : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term (∅ ,, τ₃) (∅ ,, τ₄) → Term (∅ ,, τ₁ ⇐ τ₄) (∅ ,, τ₂ ⇐ τ₃)
  ⇒U : Term (∅ ,, τ₁) (∅ ,, τ₂) → Term (∅ ,, τ₃) (∅ ,, τ₄) → Term (∅ ,, τ₂ ⇒ τ₃) (∅ ,, τ₁ ⇒ τ₄)

Visible : Context n → Set
Visible {n} Γ = ∃ λ τ → Γ ≅ ∅ ,, τ

visibility : Term Γ Δ → Visible Γ ⊎ Visible Δ
visibility var = inj₁ (_ , refl)
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

cut : Term Γ (∅ ,, τ) → Term (∅ ,, τ) Δ → Term Γ Δ
cutL : Term Γ₁ (∅ ,, τ) → Term (Γ₂ ,, τ) Δ → Term (Γ₁ ++ Γ₂) Δ
cutR : Term Γ (Δ₁ ,, τ) → Term (∅ ,, τ) Δ₂ → Term Γ (Δ₂ ++ Δ₁)

cut var y = y
cut (⊗L x) y = ⊗L (cutL x y)
cut (⅋L (left done) x₁ x₂) y = ⅋L all-lefts (cut x₁ y) x₂
cut (⅋L (right done) x₁ x₂) y = ⅋L all-rights x₁ (cut x₂ y)
cut (1L x) y = 1L (cut x y)
cut (⊕L x x₁) y = ⊕L (cut x y) (cut x₁ y)
cut (&L₁ x) y = &L₁ (cut x y)
cut (&L₂ x) y = &L₂ (cut x y)
cut 0L _ = 0L
cut (⇒L x x₁) y = ⇒L x (cut x₁ y)
cut (⊥R x) ⊥L = x
cut 1R (1L y) = y
cut (&R x x₁) (&L₁ y) = cut x y
cut (&R x x₁) (&L₂ y) = cut x₁ y
cut (⊕R₁ x) (⊕L y y₁) = cut x y
cut (⊕R₂ x) (⊕L y y₁) = cut x y₁
cut (⇒R x) (⇒L y y₁) = cut y (cut x y₁)
cut (⇒R x) (⇒U y y₁) = ⇒R (cut y (cut x y₁))
cut (⇐R x x₁) (⇐L y) = cut x (cut y x₁)
cut (⇐R x x₁) (⇐U y y₁) = ⇐R (cut x y) (cut y₁ x₁)
cut (⇐U x x₁) (⇐L y) = ⇐L (cut x (cut y x₁))
cut (⇐U x x₁) (⇐U y y₁) = ⇐U (cut x y) (cut y₁ x₁)
cut (⇒U x x₁) (⇒L y y₁) = ⇒L (cut y x) (cut x₁ y₁)
cut (⇒U x x₁) (⇒U y y₁) = ⇒U (cut y x) (cut x₁ y₁)
cut (⅋R (⅋L (left (left done)) x₁ x₂)) y = ⅋L all-lefts (cut (⅋R x₁) y) x₂
cut (⅋R (⅋L (left (right done)) x₁ x₂)) (⅋L x y y₁) = ⅋L (reverse-exch x) (cut x₁ y₁) (cut x₂ y)
cut (⅋R (⅋L (right (left done)) x₁ x₂)) (⅋L x y y₁) = ⅋L x (cut x₁ y) (cut x₂ y₁)
cut (⅋R (⅋L (right (right done)) x₁ x₂)) y = ⅋L all-rights x₁ (cut (⅋R x₂) y)
cut (⅋R (⊕L x x₁)) y = ⊕L (cut (⅋R x) y) (cut (⅋R x₁) y)
cut (⅋R (&L₁ x)) y = &L₁ (cut (⅋R x) y)
cut (⅋R (&L₂ x)) y = &L₂ (cut (⅋R x) y)
cut (⅋R 0L) _ = 0L
cut (⅋R (⇒L x x₁)) y = ⇒L x (cut (⅋R x₁) y)
cut (⊗R x x₁ x₂) (⊗L (⊗R (left (right done)) y y₁)) = ⊗R (reverse-exch x) (cut x₂ y) (cut x₁ y₁)
cut (⊗R x x₁ x₂) (⊗L (⊗R (right (left done)) y y₁)) = ⊗R x (cut x₁ y) (cut x₂ y₁)
cut x var = x
cut x (⅋R y) = ⅋R (cutR x y)
cut x (⊗R (left done) y₁ y₂) = ⊗R all-lefts (cut x y₁) y₂
cut x (⊗R (right done) y₁ y₂) = ⊗R all-rights y₁ (cut x y₂)
cut x (⊥R y) = ⊥R (cut x y)
cut x (&R y y₁) = &R (cut x y) (cut x y₁)
cut x (⊕R₁ y) = ⊕R₁ (cut x y)
cut x (⊕R₂ y) = ⊕R₂ (cut x y)
cut _ ⊤R = ⊤R
cut x (⇐R y y₁) = ⇐R (cut x y) y₁
cut x (⊗L (⊗R (left (left done)) y y₁)) = ⊗R all-lefts (cut x (⊗L y)) y₁
cut x (⊗L (⊗R (right (right done)) y y₁)) = ⊗R all-rights y (cut x (⊗L y₁))
cut x (⊗L (&R y y₁)) = &R (cut x (⊗L y)) (cut x (⊗L y₁))
cut x (⊗L (⊕R₁ y)) = ⊕R₁ (cut x (⊗L y))
cut x (⊗L (⊕R₂ y)) = ⊕R₂ (cut x (⊗L y))
cut _ (⊗L ⊤R) = ⊤R
cut x (⊗L (⇐R y y₁)) = ⇐R (cut x (⊗L y)) y₁

postulate
  tedious : Exch Γ Γ₁ (∅ ++ Γ₂) → Exch Γ Γ₁ Γ₂
  tedious2 : Exch Γ (∅ ++ Γ₁) Γ₂ → Exch Γ Γ₁ Γ₂

cutL {Γ₂ = ∅} x y = cut x y
cutL {Γ₂ = _ ,, _} x (⊗R (left p) y y₁) = ⊗R (tedious (over p all-lefts)) (cutL x y) y₁
cutL {Γ₂ = _ ,, _} x (⊗R (right p) y y₁) = ⊗R (tedious2 (over p all-rights)) y (cutL x y₁)
cutL {Γ₂ = _ ,, _} x (&R y y₁) = &R (cutL x y) (cutL x y₁)
cutL {Γ₂ = _ ,, _} x (⊕R₁ y) = ⊕R₁ (cutL x y)
cutL {Γ₂ = _ ,, _} x (⊕R₂ y) = ⊕R₂ (cutL x y)
cutL {Γ₂ = _ ,, _} _ ⊤R = ⊤R
cutL {Γ₂ = _ ,, _} x (⇐R y y₁) = ⇐R (cutL x y) y₁

cutR {Δ₁ = ∅} x y = cut x y
cutR {Δ₁ = _ ,, _} (⅋L (left p) x x₁) y = ⅋L (tedious (over p all-lefts)) (cutR x y) x₁
cutR {Δ₁ = _ ,, _} (⅋L (right p) x x₁) y = ⅋L (tedious2 (over p all-rights)) x (cutR x₁ y)
cutR {Δ₁ = _ ,, _} (⊕L x x₁) y = ⊕L (cutR x y) (cutR x₁ y)
cutR {Δ₁ = _ ,, _} (&L₁ x) y = &L₁ (cutR x y)
cutR {Δ₁ = _ ,, _} (&L₂ x) y = &L₂ (cutR x y)
cutR {Δ₁ = _ ,, _} 0L _ = 0L
cutR {Δ₁ = _ ,, _} (⇒L x x₂) y = ⇒L x (cutR x₂ y)
