------------------------------------------------------------------------
-- Presentations of groups
--
-- Equal matrices give encodings equal by Paper-V0's rules
--
-- A Cliff₃ circuit's matrix is its encoding's up to a phase
-- (Encoding.enc-sem), proportional matrices of Paper-V0 circuits give
-- the same element of Pauli ⋊ Sp(2n, ℤ/3ℤ) (Faithful.faithful), and
-- Paper-V0 presents that group (Examples.Groups.ProjectiveClifford.
-- Qupit.Paper-V0.Presentation), so its interpretation is injective.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Bridge where

open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt ; ⊤)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Independence.Semantics.Qutrit using (Sc ; module Phases ; module Circuits)
open import Examples.Independence.Qutrit-Clifford.Syntactics using (Circuit)
import Examples.Independence.Qutrit-Clifford.Semantics as Sem
open import Examples.Independence.Qutrit-Clifford.Encoding using (E₀ʷ ; enc-sem)
open import Examples.Independence.Qutrit-Clifford.Faithful using (faithful)
import Examples.Independence.Qutrit-Clifford.P3 as P3

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Presentation
  P3.p-3 P3.p-prime P3.g* P3.g-gen as PV0
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  P3.p-3 P3.p-prime P3.g* P3.g-gen as Pap
open Pap.Clifford-Relations renaming (_QRel,_===_ to _V0,_===_)

open Phases (λ _ → ⊤) tt (λ _ _ → tt) (λ _ → tt)
  using (≈-trans ; ≈-sym ; phased) renaming (_≈_ to _≈ᵖ_)

private
  variable
    n : ℕ

  module X = Circuits Sem.val

  -- Exact equality is equality up to the phase 0.
  exact : {s t : Sc n} → s Sem.≈ t → s ≈ᵖ t
  exact e = phased (X.Exact._≈_.phase e) tt (X.Exact._≈_.agree e)

-- Circuits with equal matrices have encodings equal by Paper-V0's rules.
bridge : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ →
         PB._≈_ (n V0,_===_) (E₀ʷ w) (E₀ʷ v)
bridge {n} {w} {v} e = P.injective (proj₁ same , proj₂ same)
  where
  module P = GroupMorphisms.IsGroupIsomorphism (_IsPresentationOf_.iso (PV0.presentation n))
  same = faithful (E₀ʷ w) (E₀ʷ v) (≈-trans (≈-sym (enc-sem w)) (≈-trans (exact e) (enc-sem v)))
