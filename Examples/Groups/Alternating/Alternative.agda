------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 4 with its second relation replaced by (ω ↑ • ω)² = 1.
--
-- After Theorem 4 Lafont notes that its second relation can be
-- replaced by ω₂ ω₁ ω₂ ω₁ = id (p. 267, drawn top to bottom).  Restricted
-- to n wires this is his presentation of 𝔄ₙ on p. 268: generators ω₁,
-- …, ω_{n−2} with ω_i³ = 1, (ω_i ω_{i+1})² = 1, ω_i ω_{i+2} ω_i =
-- ω_{i+1} ω_i ω_{i+2} and ω_i ω_j = ω_j ω_i for j > i + 2, products
-- in composition order.  Read in diagram order the second is
-- (ω_{i+1} ω_i)² = 1, which is square below, and the third is far.
--
-- Theorem 4's second relation follows from square and ω³ = 1, so the
-- rules of Fig. 10 hold here by Derivations, and Presentation shows
-- that these relations present 𝔄ₙ too.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Alternative where

open import Data.Nat using (ℕ)
open import Notations using (₃₊ ; ₄₊)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (WRel ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Alternating.Derivations
  using (step ; module FromRelations)
open import Examples.Groups.Alternating.Rules using (Fig10)
open import Examples.Groups.Alternating.Syntactics
  using ( Gen ; ω ; _↑ ; ₅₊ ; _∣_⊢_≈_ ; module Lift-Relation )

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The relations

infix 4 _SRel′,_===_
data _SRel′,_===_ : (n : ℕ) → WRel (Gen n) where
  order  : (₃₊ n) SRel′, ω • ω • ω === ε
  square : (₄₊ n) SRel′, ω ↑ • ω • ω ↑ • ω === ε
  far    : (₅₊ n) SRel′, ω • ω ↑ ↑ • ω === ω ↑ ↑ • ω • ω ↑

private module LR′ = Lift-Relation _SRel′,_===_

-- The relations with the structural rules.
open LR′ public using () renaming (_VRel,_===_ to _VRel′,_===_)

------------------------------------------------------------------------
-- Theorem 4's second relation, and the rules of Fig. 10

near : ∀ {n} → _SRel′,_===_ ∣ ₄₊ n ⊢ ω • ω ↑ • ω ≈ ω ↑ • ω ↑
near {n} = begin
  ω • ω ↑ • ω                     ≈⟨ step ε (ω • ω ↑ • ω)
                                          (PB.sym (LR′.lemma-cong↑ _ _
                                            (PB.axiom (LR′.srel order))))
                                          Eq.refl Eq.refl ⟩
  ω ↑ • ω ↑ • ω ↑ • ω • ω ↑ • ω   ≈⟨ step (ω ↑ • ω ↑) ε
                                          (PB.axiom (LR′.srel square))
                                          Eq.refl Eq.refl ⟩
  ω ↑ • ω ↑                       ∎
  where open SR (PP.word-setoid ((₄₊ n) VRel′,_===_))

fig10′ : Fig10 _SRel′,_===_
fig10′ = FromRelations.fig10 _SRel′,_===_
  (PB.axiom (LR′.srel order)) near (PB.axiom (LR′.srel far))
