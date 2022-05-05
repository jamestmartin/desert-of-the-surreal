{-# OPTIONS --with-K --injective-type-constructors #-}
-- Cut admissibility goes in a separate file because type checking it is *really slow*!
-- Exchange admissibility also goes here so I can *pretend* there's a logical reason for it.
module Basic.Admissible where

open import Basic
open import SqEq

-- TODO: Prove that exchange is admissible.
--`exch : Permute Γ Γ' → Permute Δ Δ' → Term Γ Δ → Term Γ' Δ'`

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
