------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations on three qubits: rigid, and merged on the top wire
-- (Clément, Appendix E.5 at n = 3, from Lemma D.2)
--
-- On three wires the rotations are CCZX and CCXZ.  The swap of the
-- wires 1 2 passes CCZX by (127), hence its inverse CCXZ ((117),
-- (118)), so both are rigid on wire 0 (`rig₃`, RotRigid).  The top
-- merges are a two-wire evaluation on two wires and (136), resp. (138)
-- conjugated by X on wire 2, on three (`tm₃`).  Only completeness on two
-- qubits is used.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.Kit
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Nat using (zero ; suc ; _<_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L ; L-comm)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq127 ; eq136 ; eq138 ; °CCXZ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; F ; TopMerge)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BaseRotMerge using (e-zx1 ; e-xz1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3)
import Examples.Groups.Real-Clifford+CH.GeneralN.RotRigid as RotRigid

open Tools (3 VRel,_===_)
open WordAlgebra (3 VRel,_===_) using (comm-inv)

private
  ≡→≈ : ∀ {a b : Circuit 3} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- Rigid on wire 0

s12₃ : ∀ β → Ex ↑ • rot {0} β ≈ rot β • Ex ↑
s12₃ true  = sym eq127
s12₃ false = comm-inv eq117 eq118 (sym eq127)

rig₃ : ∀ β → Rigid 1 (rot {0} β)
rig₃ = RotRigid.rot-rigid canon3 s12₃

------------------------------------------------------------------------
-- The top merges

-- (138) conjugated by X on wire 2: the other order.
eq138′ : °CCXZ • CCXZ ≈ L (ΛXZ 1)
eq138′ = begin
  °CCXZ • CCXZ            ≈⟨ sym (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ CCXZ)) ⟩
  N₂.⟪ CCXZ • °CCXZ ⟫     ≈⟨ N₂.⟪⟫-cong eq138 ⟩
  N₂.⟪ L (ΛXZ 1) ⟫        ≈⟨ N₂.⟪⟫-fix (sym (L-comm (ΛXZ 1) X)) ⟩
  L (ΛXZ 1) ∎

private
  top₂ : ∀ β → placeAt 2 (F β 1) ≈ L (F β 1)
  top₂ true  = trans (placeAt-top (ΛZX 1)) (≡→≈ Eq.refl)
  top₂ false = trans (placeAt-top (ΛXZ 1)) (≡→≈ Eq.refl)

tm₃ : ∀ β K → K < 2 → TopMerge β K
tm₃ true  zero          _ =
  SS.Below.by-sem₀ 2 (s≤s (s≤s z≤n)) complete₂ ((Xat 1 • ΛZX 1 • Xat 1) • ΛZX 1) (placeAt 1 (ΛZX 0)) (Evaluated.same e-zx1)
tm₃ false zero          _ =
  SS.Below.by-sem₀ 2 (s≤s (s≤s z≤n)) complete₂ ((Xat 1 • ΛXZ 1 • Xat 1) • ΛXZ 1) (placeAt 1 (ΛXZ 0)) (Evaluated.same e-xz1)
tm₃ true  (suc zero)    _ = trans eq136 (sym (top₂ true))
tm₃ false (suc zero)    _ = trans eq138′ (sym (top₂ false))
tm₃ β     (suc (suc K)) (s≤s (s≤s ()))
