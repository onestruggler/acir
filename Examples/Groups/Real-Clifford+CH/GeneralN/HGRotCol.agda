------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget, as a statement (Clément,
-- Appendix E.5, rule (38))
--
-- The gadget of Definition 8.3, the decoded H_[0,1] H_[3,2], is the H
-- gate with its H on wire 0 and its box wire 1 (Layout's S, the H gate
-- under the swap of the wires 0 1), every other control white (`gcol`).
-- `HGRot m` says that a rotation placed on any target t and coloured s
-- commutes with it as soon as s is black on some wire j ≥ 2 other than
-- t, where the gadget is white: the paper's (348)–(350) with x ≠ y.
-- Like RotCol, this module has no parameters, so that the proof at width
-- 5 + k (HGAnywhere) and the rule that uses it (Lemma88.Rule38) spell
-- the statement alike.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol where

open import Data.Bool using (true ; false)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; _≤_)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₁₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)

-- The gadget's colouring, and the gadget.
gcol : ∀ m → Bits (₃₊ m)
gcol m = true ∷ true ∷ replicate (₁₊ m) false

gadgetG : ∀ m → Circuit (₃₊ m)
gadgetG m = col (gcol m) (Ex ↓ • ΛH (₁₊ m) • Ex ↓)

HGRot : ℕ → Set
HGRot m =
  ∀ β (u : Word (S.Gen (₃₊ m))) (t : Fin (₃₊ m)) → perm u ⟨$⟩ʳ t ≡ 0F → (s : Bits (₃₊ m)) →
  lookupℕ (toℕ t) s ≡ true → (j : Fin (₃₊ m)) → 2 ≤ toℕ j → j ≢ t → lookupℕ (toℕ j) s ≡ true →
  (₃₊ m) ⊢ place u s (rot β) • gadgetG m ≈ gadgetG m • place u s (rot β)

-- The transposition of the wires 0 3, and the network putting the box
-- on wire 2 (K below); where they send wires, at a variable width (at
-- a width 3 + m the conversion checker unfolds much further).
t03 : ∀ {n} → Word (S.Gen (₄₊ n))
t03 = S.σ • (S.σ S.↑ • ((S.σ S.↑) S.↑ • (S.σ S.↑ • S.σ)))

k₀ : ∀ {n} → Word (S.Gen (₄₊ n))
k₀ = S.σ S.↑ • S.σ

perm-t03 : ∀ {n} → perm {₄₊ n} t03 ⟨$⟩ʳ sF (sF (sF 0F)) ≡ 0F
perm-t03 = Eq.refl

cond-K : ∀ {n} → perm {₄₊ n} k₀ ⟨$⟩ʳ (perm (revS (t03 • k₀)) ⟨$⟩ʳ 0F) ≡ 0F
cond-K = Eq.refl
