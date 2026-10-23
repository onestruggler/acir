------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on four qubits: every rule of P′ decodes
--
-- Lemma88.HybridRules derives every rule of P′ from facts about the
-- decoded letters at the top pair N − 2, N − 1.  At four wires (N = 16,
-- the top pair 14, 15) the K-free facts are Four.Facts, and the facts
-- about the hybrid are Four.Facts.H1, each a transport of a class fact
-- derived at the gadget level: the far facts, the shifts, the pair
-- scalar, the core facts k p = p h k and k³ = ε, and ki-sq and ki-yb at
-- their canonical positions (the four-wire rules hyb-sq and hyb-yb).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Proofs ; Win ; get)
open import Examples.Groups.Clifford+CS.Four.CStmt using (clemmas)

module Examples.Groups.Clifford+CS.Four.Hybrid (C : Proofs clemmas) where

open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Decoding 0 using (dPP₁ ; dPP₁′ ; lo₁ ; hi₁ ; dKI₁)
open import Examples.Groups.Clifford+CS.CompletenessInduction using (DWD)
open import Examples.Groups.Clifford+CS.Four.Facts C using (facts)
open import Examples.Groups.Clifford+CS.Four.Facts.H1 C
  using (d-far-p ; d-far-l ; d-far-k ; d-shift ; d-sc ; i-cp-14 ; i-c3-14 ; i-sq-14 ; i-yb-14)
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
import Examples.Groups.Clifford+CS.Lemma88.HybridRules as HR

open Tools ((₄₊ 0) VRel,_===_) using (trans ; by-assoc)

private
  module R = HR ((₄₊ 0) VRel,_===_) 12 dPP₁ dPP₁′ lo₁ hi₁ dKI₁ ≤-refl

-- The far facts at the top pair.
topFar : HTop.TopFar ((₄₊ 0) VRel,_===_) 16 dPP₁ dPP₁′ lo₁ hi₁ dKI₁
topFar = record { far-p = λ {j} → d-far-p j ; far-l = λ {j} → d-far-l j }

private
  module Rules = R.Proofs facts topFar d-sc (λ {j} → d-shift j) (λ {j} → d-far-k j)
                   i-cp-14 i-c3-14
                   (trans (by-assoc Eq.refl) i-sq-14)
                   (trans (by-assoc Eq.refl) (trans i-yb-14 (by-assoc Eq.refl)))

-- Lemma 8.8 on four qubits.
dwd₄ : DWD 0
dwd₄ = Rules.rules
