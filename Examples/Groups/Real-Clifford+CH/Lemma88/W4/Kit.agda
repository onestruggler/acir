------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations on four qubits: rigid, and merged on the top wire
-- (Clément, Appendix E.5 at n = 4, from Lemma D.5)
--
-- On four wires the rotations are Lemma D.5's ZX₃ and XZ₃.  The swaps
-- of the controls pass them ((214), (215)), so they are rigid on wire 0
-- (`rig₄`, RotRigid).  The top merges are two- and three-wire
-- evaluations on two and three wires and (223), (224) on four
-- (`tm₄`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Kit
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Nat using (zero ; suc ; _<_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (eq215 ; eq215′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃ using (eq223 ; eq224)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; TopMerge)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BaseRotMerge using (e-zx1 ; e-xz1 ; e-zx2 ; e-xz2)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
import Examples.Groups.Real-Clifford+CH.GeneralN.RotRigid as RotRigid

open Tools (4 VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit 4} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- Rigid on wire 0

s12₄ : ∀ β → Ex ↑ • rot {1} β ≈ rot β • Ex ↑
s12₄ true  = sym eq215
s12₄ false = sym eq215′

rig₄ : ∀ β → Rigid 1 (rot {1} β)
rig₄ = RotRigid.rot-rigid canon4 s12₄

------------------------------------------------------------------------
-- The top merges

tm₄ : ∀ β K → K < 3 → TopMerge β K
tm₄ true  zero                _ =
  SS.Below.by-sem₀ 2 (s≤s (s≤s z≤n)) complete₂ ((Xat 1 • ΛZX 1 • Xat 1) • ΛZX 1) (placeAt 1 (ΛZX 0)) (Evaluated.same e-zx1)
tm₄ false zero                _ =
  SS.Below.by-sem₀ 2 (s≤s (s≤s z≤n)) complete₂ ((Xat 1 • ΛXZ 1 • Xat 1) • ΛXZ 1) (placeAt 1 (ΛXZ 0)) (Evaluated.same e-xz1)
tm₄ true  (suc zero)          _ =
  SS.Below.by-sem₀ 3 (s≤s (s≤s (s≤s z≤n))) complete₃ ((Xat 2 • ΛZX 2 • Xat 2) • ΛZX 2) (placeAt 2 (ΛZX 1)) (Evaluated.same e-zx2)
tm₄ false (suc zero)          _ =
  SS.Below.by-sem₀ 3 (s≤s (s≤s (s≤s z≤n))) complete₃ ((Xat 2 • ΛXZ 2 • Xat 2) • ΛXZ 2) (placeAt 2 (ΛXZ 1)) (Evaluated.same e-xz2)
tm₄ true  (suc (suc zero))    _ = trans eq223 (sym (trans (placeAt-top (ΛZX 2)) (≡→≈ Eq.refl)))
tm₄ false (suc (suc zero))    _ = trans eq224 (sym (trans (placeAt-top (ΛXZ 2)) (≡→≈ Eq.refl)))
tm₄ β     (suc (suc (suc K))) (s≤s (s≤s (s≤s ())))
