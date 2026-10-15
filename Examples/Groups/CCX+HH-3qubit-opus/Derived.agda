------------------------------------------------------------------------
-- Presentations of groups
--
-- The identities that Completeness takes as a record, at level 1: the
-- Coxeter relations and the identities of Toffoli.Lemmas, derived from
-- Figure 4 at level 0 and lifted, and two about CCZ, derived from
-- Figure 7's (83).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Derived where

open import Data.List.Base using (List ; [] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Lift using (lift₀₁)
open import Examples.Groups.CCX+HH-3qubit-opus.Completeness using (Derived)
import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Base as B0
import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Lemmas as L0
open import Examples.Groups.CCX+HH-3qubit-opus.Toffoli.Coxeter using (coxeter₁)
import Examples.Groups.CCX+HH-3qubit-opus.Engine

open PB _===₁⁺_ using (_≈_ ; sym ; axiom)

private
  module E1 = Examples.Groups.CCX+HH-3qubit-opus.Engine _===₁⁺_ code code-inj
  open E1 using (Eqn ; derive ; rw ; to≈ ; of⁼ ; ax⁼ ; sym⁼)

  sq0 sq1 sq2 e83 : Eqn
  sq0 = ax⁼ (fig4 r21)
  sq1 = of⁼ (lift₀₁ (B0.to≈ B0.x1sq {w = X1 • X1} {v = ε} Eq.refl Eq.refl))
  sq2 = of⁼ (lift₀₁ (B0.to≈ B0.x2sq {w = X2 • X2} {v = ε} Eq.refl Eq.refl))
  e83 = ax⁼ (fig7 r83)

  -- CCZ, from (-1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀.
  cczr′ : Eqn
  cczr′ = derive
    (X₂ ∷ X₁ ∷ X₀ ∷ X₀ ∷ X₁ ∷ X₂ ∷ CCZ ∷ X₂ ∷ X₁ ∷ X₀ ∷ X₀ ∷ X₁ ∷ X₂ ∷ [])
    (CCZ ∷ [])
    ( rw 2 sq0
    ∷ rw 1 sq1
    ∷ rw 0 sq2
    ∷ rw 3 sq0
    ∷ rw 2 sq1
    ∷ rw 1 sq2
    ∷ [])
    Eq.refl

  cczsq : Eqn
  cczsq = derive
    (CCZ ∷ CCZ ∷ [])
    []
    ( rw 0 (sym⁼ cczr′)
    ∷ rw 13 (sym⁼ cczr′)
    ∷ rw 12 sq2
    ∷ rw 11 sq1
    ∷ rw 10 sq0
    ∷ rw 3 e83
    ∷ rw 2 sq0
    ∷ rw 1 sq1
    ∷ rw 0 sq2
    ∷ [])
    Eq.refl

invol₁ : (g : G₁) → [ g ]ʷ • [ g ]ʷ ≈ ε
invol₁ X₀ = lift₀₁ (B0.invol X₀)
invol₁ X₁ = lift₀₁ (B0.invol X₁)
invol₁ X₂ = lift₀₁ (B0.invol X₂)
invol₁ Z₀ = lift₀₁ (B0.invol Z₀)
invol₁ Z₁ = lift₀₁ (B0.invol Z₁)
invol₁ Z₂ = lift₀₁ (B0.invol Z₂)
invol₁ CX₀₁ = lift₀₁ (B0.invol CX₀₁)
invol₁ CX₀₂ = lift₀₁ (B0.invol CX₀₂)
invol₁ CX₁₀ = lift₀₁ (B0.invol CX₁₀)
invol₁ CX₁₂ = lift₀₁ (B0.invol CX₁₂)
invol₁ CX₂₀ = lift₀₁ (B0.invol CX₂₀)
invol₁ CX₂₁ = lift₀₁ (B0.invol CX₂₁)
invol₁ CZ₀₁ = lift₀₁ (B0.invol CZ₀₁)
invol₁ CZ₀₂ = lift₀₁ (B0.invol CZ₀₂)
invol₁ CZ₁₂ = lift₀₁ (B0.invol CZ₁₂)
invol₁ CCX₀₁ = lift₀₁ (B0.invol CCX₀₁)
invol₁ CCX₀₂ = lift₀₁ (B0.invol CCX₀₂)
invol₁ CCX₁₂ = lift₀₁ (B0.invol CCX₁₂)
invol₁ K₀₁ = lift₀₁ (B0.invol K₀₁)
invol₁ K₁₂ = lift₀₁ (B0.invol K₁₂)
invol₁ SW₀₁ = lift₀₁ (B0.invol SW₀₁)
invol₁ SW₀₂ = lift₀₁ (B0.invol SW₀₂)
invol₁ SW₁₂ = lift₀₁ (B0.invol SW₁₂)
invol₁ NK = axiom (fig7 r84)
invol₁ CCZ = to≈ cczsq {w = CCZw • CCZw} {v = ε} Eq.refl Eq.refl

derived : Derived
derived = record
  { coxeter = coxeter₁
  ; invol   = invol₁
  ; cx12r = lift₀₁ (B0.to≈ L0.cx12r {w = CX12} {v = T 2 • CCX01} Eq.refl Eq.refl)
  ; cx02r = lift₀₁ (B0.to≈ L0.cx02r {w = CX02} {v = T 4 • CCX01} Eq.refl Eq.refl)
  ; x2r = lift₀₁ (B0.to≈ L0.x2r {w = X2} {v = T 0 • CCX01 • CX12 • CX02} Eq.refl Eq.refl)
  ; ccx02r = lift₀₁ (B0.to≈ L0.ccx02r {w = CCX02} {v = CX12 • T 5 • CX12} Eq.refl Eq.refl)
  ; cx21r = lift₀₁ (B0.to≈ L0.cx21r {w = CX21} {v = CX12 • T 1 • CX12 • CCX02} Eq.refl Eq.refl)
  ; cx01r = lift₀₁ (B0.to≈ L0.cx01r {w = CX01} {v = SW12 • CX02 • SW12} Eq.refl Eq.refl)
  ; ccx12r = lift₀₁ (B0.to≈ L0.ccx12r {w = CCX12} {v = CX02 • CX01 • T 3 • CX02 • CX01} Eq.refl Eq.refl)
  ; cx10r = lift₀₁ (B0.to≈ L0.cx10r {w = CX10} {v = CCX12 • CX12 • CCX12 • CX12} Eq.refl Eq.refl)
  ; x0r = lift₀₁ (B0.to≈ L0.x0r {w = X0} {v = SW02 • X2 • SW02} Eq.refl Eq.refl)
  ; cx20r   = sym (lift₀₁ (B0.to≈ B0.cx20def {w = SW01 • CX21 • SW01} {v = CX20} Eq.refl Eq.refl))
  ; cczr    = sym (to≈ cczr′ {w = X2 • X1 • X0 • m0 • X0 • X1 • X2} {v = CCZw} Eq.refl Eq.refl)
  }
