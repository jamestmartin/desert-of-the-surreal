{-# OPTIONS --with-K --injective-type-constructors #-}
module Basic where

open import SqEq

import Data.Empty as E
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.HeterogeneousEquality as HetEq
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary

private variable n n₁ n₂ n₃ n₄ n₅ n₆ : ℕ

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

Visible : Context n → Set
Visible {n} Γ = ∃ λ τ → Γ ≅ ∅ ,, τ

-- Visibility follows syntactically from the operational rules.
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

-- I begin on the left hand side. The dual rules on the RHS are presented below.
-- (Aside: it would be easier to read with the rules next to their duals, but I think that
-- makes the function have worse definitional equalities because of exact-splitting.)
cut var y = y
-- Traverse down the proof tree.
cut (⊗L x) y = ⊗L (cutL x y)   -- NB: This is the only place `cut` calls `cutL`.
cut (⅋L (left done) x₁ x₂) y = ⅋L all-lefts (cut x₁ y) x₂
cut (⅋L (right done) x₁ x₂) y = ⅋L all-rights x₁ (cut x₂ y)
cut (1L x) y = 1L (cut x y)
cut (⊕L x x₁) y = ⊕L (cut x y) (cut x₁ y)
cut (&L₁ x) y = &L₁ (cut x y)
cut (&L₂ x) y = &L₂ (cut x y)
cut 0L _ = 0L
cut (⇒L x x₁) y = ⇒L x (cut x₁ y)
-- Constructors annihilate eliminators.
cut (⊥R x) ⊥L = x
cut 1R (1L y) = y
cut (&R x x₁) (&L₁ y) = cut x y
cut (&R x x₁) (&L₂ y) = cut x₁ y
cut (⊕R₁ x) (⊕L y y₁) = cut x y
cut (⊕R₂ x) (⊕L y y₁) = cut x y₁
-- `⇒U` and `⇐U` seem to be neutral and are annihilated by either constructors *or* eliminators.
cut (⇒R x) (⇒L y y₁) = cut y (cut x y₁)
cut (⇒R x) (⇒U y y₁) = ⇒R (cut y (cut x y₁))
cut (⇐R x x₁) (⇐L y) = cut x (cut y x₁)
cut (⇐R x x₁) (⇐U y y₁) = ⇐R (cut x y) (cut y₁ x₁)
cut (⇐U x x₁) (⇐L y) = ⇐L (cut x (cut y x₁))
cut (⇐U x x₁) (⇐U y y₁) = ⇐U (cut x y) (cut y₁ x₁)
cut (⇒U x x₁) (⇒L y y₁) = ⇒L (cut y x) (cut x₁ y₁)
cut (⇒U x x₁) (⇒U y y₁) = ⇒U (cut y x) (cut x₁ y₁)
-- There are *two* (co)terms introduced by `⅋L` which need to be cut into `⅋R`.
-- (Note that `y` is always `⅋L`, but in two of the cases it is not necessary to match against it.)
-- We either cut *both* terms down one side by propogating `y` and its context down that side
-- via introducing a *new* ⅋R, or we cut one sub-term of `y` down one side and the other sub-term down
-- the other side. Either way, the context of each sub-term is propogated downard via `Exch`.
cut (⅋R (⅋L (left (left done)) x₁ x₂)) y = ⅋L all-lefts (cut (⅋R x₁) y) x₂
-- The left sub-term goes down the right side and the right sub-term goes down the right side,
-- so we need to reverse the order of the contexts.
cut (⅋R (⅋L (left (right done)) x₁ x₂)) (⅋L x y y₁) = ⅋L (reverse-exch x) (cut x₁ y₁) (cut x₂ y)
cut (⅋R (⅋L (right (left done)) x₁ x₂)) (⅋L x y y₁) = ⅋L x (cut x₁ y) (cut x₂ y₁)
cut (⅋R (⅋L (right (right done)) x₁ x₂)) y = ⅋L all-rights x₁ (cut (⅋R x₂) y)
-- Traversing down the proof tree as we did before, only we're cutting in two terms instead of one
-- by introducing a new ⅋R at every step.
cut (⅋R (⊕L x x₁)) y = ⊕L (cut (⅋R x) y) (cut (⅋R x₁) y)
cut (⅋R (&L₁ x)) y = &L₁ (cut (⅋R x) y)
cut (⅋R (&L₂ x)) y = &L₂ (cut (⅋R x) y)
cut (⅋R 0L) _ = 0L
cut (⅋R (⇒L x x₁)) y = ⇒L x (cut (⅋R x₁) y)
-- Dual rules.
cut x var = x
cut x (⅋R y) = ⅋R (cutR x y)   -- NB: This is the only place `cut` calls `cutR`.
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
-- Looks like the dual rules for ⊗R compared to ⅋R are simpler for whatever reason? I'm not sure why.
cut (⊗R x x₁ x₂) (⊗L (⊗R (left (right done)) y y₁)) = ⊗R (reverse-exch x) (cut x₂ y) (cut x₁ y₁)
cut (⊗R x x₁ x₂) (⊗L (⊗R (right (left done)) y y₁)) = ⊗R x (cut x₁ y) (cut x₂ y₁)

cutL {Γ₂ = ∅} x y = cut x y
cutL {Γ₂ = _ ,, _} x (⊗R (left p) y y₁) = ⊗R (exch-coe₁ (over p all-lefts)) (cutL x y) y₁
cutL {Γ₂ = _ ,, _} x (⊗R (right p) y y₁) = ⊗R (exch-coe₂ (over p all-rights)) y (cutL x y₁)
cutL {Γ₂ = _ ,, _} x (&R y y₁) = &R (cutL x y) (cutL x y₁)
cutL {Γ₂ = _ ,, _} x (⊕R₁ y) = ⊕R₁ (cutL x y)
cutL {Γ₂ = _ ,, _} x (⊕R₂ y) = ⊕R₂ (cutL x y)
cutL {Γ₂ = _ ,, _} _ ⊤R = ⊤R
cutL {Γ₂ = _ ,, _} x (⇐R y y₁) = ⇐R (cutL x y) y₁

cutR {Δ₁ = ∅} x y = cut x y
cutR {Δ₁ = _ ,, _} (⅋L (left p) x x₁) y = ⅋L (exch-coe₁ (over p all-lefts)) (cutR x y) x₁
cutR {Δ₁ = _ ,, _} (⅋L (right p) x x₁) y = ⅋L (exch-coe₂ (over p all-rights)) x (cutR x₁ y)
cutR {Δ₁ = _ ,, _} (⊕L x x₁) y = ⊕L (cutR x y) (cutR x₁ y)
cutR {Δ₁ = _ ,, _} (&L₁ x) y = &L₁ (cutR x y)
cutR {Δ₁ = _ ,, _} (&L₂ x) y = &L₂ (cutR x y)
cutR {Δ₁ = _ ,, _} 0L _ = 0L
cutR {Δ₁ = _ ,, _} (⇒L x x₂) y = ⇒L x (cutR x₂ y)

-- TODO: Prove that exchange is admissible.
--`exch : Permute Γ Γ' → Permute Δ Δ' → Term Γ Δ → Term Γ' Δ'`

-- 1L is an equivalence. (TODO: prove this is an actual inverse)
anti-1L : Term (∅ ,, 1') Δ → Term ∅ Δ
anti-1L var = 1R
anti-1L (⅋R x) = ⅋R (anti-1L x)
anti-1L (⊗R (left done) x₁ x₂) = ⊗R done (anti-1L x₁) x₂
anti-1L (⊗R (right done) x₁ x₂) = ⊗R done x₁ (anti-1L x₂)
anti-1L (1L x) = x
anti-1L (⊥R (1L ()))
anti-1L (&R x x₁) = &R (anti-1L x) (anti-1L x₁)
anti-1L (⊕R₁ x) = ⊕R₁ (anti-1L x)
anti-1L (⊕R₂ x) = ⊕R₂ (anti-1L x)
anti-1L ⊤R = ⊤R
anti-1L (⇐R x x₁) = ⇐R (anti-1L x) x₁

-- NO multiplicative EM is provable, nor indeed any such ⅋ at all.
ems-unprovable : ∀ {A B} → ¬ Term ∅ (∅ ,, A ⅋ B)
ems-unprovable (⅋R ())

-- It makes no difference if you follow from ∅ or 1 (see `anti-1L`).
ems-unprovable₂ : ∀ {A B} → ¬ Term (∅ ,, 1') (∅ ,, A ⅋ B)
ems-unprovable₂ (⅋R (1L ()))
ems-unprovable₂ (1L (⅋R ()))

-- TODO: proof similar to `anti-1L` for `⊤`
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

em-unprovable₅ : ¬ ∀ A → Term ∅ (∅ ,, A ⊕ (A ⇐ ⊤))
em-unprovable₅ em with em (⊥ ⊗ ⊥)
... | ⊕R₁ (⊗R done (⊥R ()) p₁)
... | ⊕R₂ (⇐R p ())

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
