------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget on three qubits (Clément,
-- Appendix E.5 at n = 3, rule (38), from Lemma D.2)
--
-- On three wires the gadget is the CH from wire 2, white, onto wire 0:
-- °CH₂₀, written as the colouring of CH₂₀ black on the wires 0 1 and
-- white on wire 2.  A rotation separated from it on wire 2 has its
-- target on wire 0 or wire 1 and is, in the frame of the identity
-- network, the canonical rotation coloured, resp. that under the swap
-- of the wires 0 1 (PlaceFrames.frame-0, frame-1).  Target on wire 0:
-- °CH₂₀ passes CH ((135) under X on wire 2) and CZ₂₀ (a two-wire
-- evaluation on the outer pair), hence both rotations; X on wire 1 does
-- not count, since it passes CH₂₀ (`E0`).  Target on wire 1: under the
-- lower swap the gadget is CH ↑ white on wire 2, which passes the
-- rotations white on wire 2 (CH↑-°CCZX, CH↑-°CCXZ); white on wire 1 as
-- well, it is that conjugated by X on its target, Z ↑ ↑ • Z ↑ • CH ↑ •
-- Z ↑ (a two-wire evaluation), whose other factors the rotations white
-- on wire 2 pass too (`E1`).  Only completeness on two qubits is used.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.HG
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Nat using (s≤s ; z≤n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂
  using (O ; O-sem ; O-• ; U-sem ; L-comm ; X↑-O ; by-sem₀)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq119 ; eq120 ; eq135 ; °CCZX ; °CCXZ ; °CH₂₀ ; N₂-O ; CZ₂₀-Z↓ ; Z↑↑-CZ₂₀ ;
         CH↑-°CCZX ; CH↑-°CCXZ ; module N₁ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (swapAt-negsB ; swB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (col-rel ; place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (conj-swap ; frame-0 ; frame-1)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGRotCol using (HGRot)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Kit complete₂ using (rig₃)

open Tools (3 VRel,_===_)
open WordAlgebra (3 VRel,_===_) using (comm-abab)

private
  module S₀₁ = Conj {3} Ex Ex²

  R : Bool → Circuit 3
  R = rot {0}

  °R : Bool → Circuit 3
  °R β = N₂.⟪ R β ⟫

  pass₂ : ∀ {a u v : Circuit 3} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  x12 : X ↑ ↑ • X ↑ ≈ X ↑ • X ↑ ↑
  x12 = sym (lemma-cong↑ (X • X ↑) (X ↑ • X) (X-↑ X))

  -- The colouring black on wire 0, white on the wires 1 2.
  cTFF : ∀ (w : Circuit 3) → col (true ∷ false ∷ false ∷ []) w ≈ N₂.⟪ N₁.⟪ w ⟫ ⟫
  cTFF w = trans (cong (back _ right-unit) (back _ (back _ right-unit)))
                 (trans (back _ (back _ (sym x12)))
                        (trans (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)
                               (conj-swap (sym x12) w)))

  cTTF : ∀ (w : Circuit 3) → col (true ∷ true ∷ false ∷ []) w ≈ N₂.⟪ w ⟫
  cTTF w = cong right-unit (back _ right-unit)

  ----------------------------------------------------------------------
  -- Target on wire 0

  N₂-CH : N₂.⟪ CH ↓ ⟫ ≈ CH ↓
  N₂-CH = N₂.⟪⟫-fix (sym (L-comm CH X))

  °CH-CH : °CH₂₀ • CH ≈ CH • °CH₂₀
  °CH-CH = N₂.⟪⟫-≈ eq135 (N₂.⟪⟫-•₂ refl N₂-CH) (N₂.⟪⟫-•₂ N₂-CH refl)

  °CH-CZ₂₀ : °CH₂₀ • CZ₂₀ ≈ CZ₂₀ • °CH₂₀
  °CH-CZ₂₀ = trans (front _ (N₂-O CH))
               (trans (sym (O-• °CH CZ))
                 (trans (O-sem (°CH • CZ) (CZ • °CH) Eq.refl)
                   (trans (O-• CZ °CH) (back _ (sym (N₂-O CH))))))

  °CH-R : ∀ β → °CH₂₀ • R β ≈ R β • °CH₂₀
  °CH-R true  = comm-abab °CH-CH °CH-CZ₂₀
  °CH-R false = comm-abab °CH-CZ₂₀ °CH-CH

  -- X on wire 1 passes CH₂₀.
  colG₀ : ∀ b → col (true ∷ b ∷ false ∷ []) CH₂₀ ≈ °CH₂₀
  colG₀ true  = cTTF CH₂₀
  colG₀ false = trans (cTFF CH₂₀) (N₂.⟪⟫-cong (N₁.⟪⟫-fix (X↑-O CH)))

  E0 : ∀ b β → R β • col (true ∷ b ∷ false ∷ []) CH₂₀ ≈ col (true ∷ b ∷ false ∷ []) CH₂₀ • R β
  E0 b β = trans (back _ (colG₀ b)) (trans (sym (°CH-R β)) (front _ (sym (colG₀ b))))

  ----------------------------------------------------------------------
  -- Target on wire 1

  CH↑-°R : ∀ β → CH ↑ • °R β ≈ °R β • CH ↑
  CH↑-°R true  = CH↑-°CCZX
  CH↑-°R false = CH↑-°CCXZ

  -- Carried back from the rotations white on wire 2.
  back₂ : ∀ β {w : Circuit 3} → °R β • w ≈ w • °R β → R β • N₂.⟪ w ⟫ ≈ N₂.⟪ w ⟫ • R β
  back₂ β e = N₂.⟪⟫-≈ e (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ (R β)) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ (R β)))

  N₂-Z↑ : N₂.⟪ Z ↑ ⟫ ≈ Z ↑
  N₂-Z↑ = N₂.⟪⟫-fix (lemma-cong↑ (X ↑ • Z) (Z • X ↑) (by-sem₀ (X ↑ • Z) (Z • X ↑) Eq.refl))

  °R-Z↑ : ∀ β → °R β • Z ↑ ≈ Z ↑ • °R β
  °R-Z↑ true  = sym (N₂.⟪⟫-≈ eq119 (N₂.⟪⟫-•₂ N₂-Z↑ refl) (N₂.⟪⟫-•₂ refl N₂-Z↑))
  °R-Z↑ false = sym (N₂.⟪⟫-≈ eq120 (N₂.⟪⟫-•₂ N₂-Z↑ refl) (N₂.⟪⟫-•₂ refl N₂-Z↑))

  -- Z on wire 2 passes the rotations white there: written out, their
  -- letters are CH and °CZ₂₀ = CZ₂₀ • Z.
  Z₂-CH : Z ↑ ↑ • CH ≈ CH • Z ↑ ↑
  Z₂-CH = sym (L-comm CH Z)

  Z₂-°CZ₂₀ : Z ↑ ↑ • °CZ₂₀ ≈ °CZ₂₀ • Z ↑ ↑
  Z₂-°CZ₂₀ = trans (back _ CZ₂₀-Z↓) (trans (pass₂ Z↑↑-CZ₂₀ (sym (L-comm Z Z))) (front _ (sym CZ₂₀-Z↓)))

  °R-Z₂ : ∀ β → °R β • Z ↑ ↑ ≈ Z ↑ ↑ • °R β
  °R-Z₂ true  = sym (trans (back _ f) (trans (comm-abab Z₂-CH Z₂-°CZ₂₀) (front _ (sym f))))
    where
    f : °CCZX ≈ CH • °CZ₂₀ • CH • °CZ₂₀
    f = N₂.⟪⟫-•₄ N₂-CH refl N₂-CH refl
  °R-Z₂ false = sym (trans (back _ f) (trans (comm-abab Z₂-°CZ₂₀ Z₂-CH) (front _ (sym f))))
    where
    f : °CCXZ ≈ °CZ₂₀ • CH • °CZ₂₀ • CH
    f = N₂.⟪⟫-•₄ refl N₂-CH refl N₂-CH

  -- X on the target of CH ↑.
  N₁-CH↑ : N₁.⟪ CH ↑ ⟫ ≈ Z ↑ ↑ • Z ↑ • CH ↑ • Z ↑
  N₁-CH↑ = U-sem (X • CH • X) (Z ↑ • Z • CH • Z) Eq.refl

  E1′ : ∀ a β → R β • col (true ∷ a ∷ false ∷ []) (CH ↑) ≈ col (true ∷ a ∷ false ∷ []) (CH ↑) • R β
  E1′ true  β = trans (back _ (cTTF (CH ↑))) (trans (back₂ β (sym (CH↑-°R β))) (front _ (sym (cTTF (CH ↑)))))
  E1′ false β =
    trans (back _ c) (trans (back₂ β (pass₂ (°R-Z₂ β) (pass₂ (°R-Z↑ β) (pass₂ (sym (CH↑-°R β)) (°R-Z↑ β)))))
          (front _ (sym c)))
    where
    c : col (true ∷ false ∷ false ∷ []) (CH ↑) ≈ N₂.⟪ Z ↑ ↑ • Z ↑ • CH ↑ • Z ↑ ⟫
    c = trans (cTFF (CH ↑)) (N₂.⟪⟫-cong N₁-CH↑)

  -- Under the lower swap the colouring moves with the wires.
  col-Ex : ∀ (s : Bits 3) (w : Circuit 3) → Ex • col s w • Ex ≈ col (swB 0 s) (Ex • w • Ex)
  col-Ex s w = S₀₁.⟪⟫-•₃ (swapAt-negsB 0 s) refl (swapAt-negsB 0 s)

  E1 : ∀ a β → (Ex • R β • Ex) • col (a ∷ true ∷ false ∷ []) CH₂₀ ≈ col (a ∷ true ∷ false ∷ []) CH₂₀ • (Ex • R β • Ex)
  E1 a β = S₀₁.⟪⟫-≈ (E1′ a β) (S₀₁.⟪⟫-•₂ refl (col-Ex (true ∷ a ∷ false ∷ []) (CH ↑)))
                               (S₀₁.⟪⟫-•₂ (col-Ex (true ∷ a ∷ false ∷ []) (CH ↑)) refl)

------------------------------------------------------------------------
-- Placed

private
  G : Circuit 3
  G = col (true ∷ true ∷ false ∷ []) CH₂₀

  -- Target on wire 0, black on wire 2.
  at₀ : ∀ β (u : Word (S.Gen 3)) → perm u ⟨$⟩ʳ 0F ≡ 0F → ∀ b →
        place u (true ∷ b ∷ true ∷ []) (R β) • G ≈ G • place u (true ∷ b ∷ true ∷ []) (R β)
  at₀ β u pu true  = trans (front _ fp) (trans (col-rel (true ∷ true ∷ true ∷ []) (true ∷ true ∷ false ∷ []) (E0 true β))
                                               (back _ (sym fp)))
    where
    fp : place u (true ∷ true ∷ true ∷ []) (R β) ≈ col (true ∷ true ∷ true ∷ []) (R β)
    fp = trans (sym (trans left-unit right-unit)) (frame-0 (rig₃ β) ε u 0F pu Eq.refl (true ∷ true ∷ true ∷ []))
  at₀ β u pu false = trans (front _ fp) (trans (col-rel (true ∷ false ∷ true ∷ []) (true ∷ true ∷ false ∷ []) (E0 false β))
                                               (back _ (sym fp)))
    where
    fp : place u (true ∷ false ∷ true ∷ []) (R β) ≈ col (true ∷ false ∷ true ∷ []) (R β)
    fp = trans (sym (trans left-unit right-unit)) (frame-0 (rig₃ β) ε u 0F pu Eq.refl (true ∷ false ∷ true ∷ []))

  -- Target on wire 1, black on wire 2.
  at₁ : ∀ β (u : Word (S.Gen 3)) → perm u ⟨$⟩ʳ sF 0F ≡ 0F → ∀ a →
        place u (a ∷ true ∷ true ∷ []) (R β) • G ≈ G • place u (a ∷ true ∷ true ∷ []) (R β)
  at₁ β u pu true  = trans (front _ fp) (trans (col-rel (true ∷ true ∷ true ∷ []) (true ∷ true ∷ false ∷ []) (E1 true β))
                                               (back _ (sym fp)))
    where
    fp : place u (true ∷ true ∷ true ∷ []) (R β) ≈ col (true ∷ true ∷ true ∷ []) (Ex • R β • Ex)
    fp = trans (sym (trans left-unit right-unit)) (frame-1 (rig₃ β) ε u (sF 0F) pu Eq.refl (true ∷ true ∷ true ∷ []))
  at₁ β u pu false = trans (front _ fp) (trans (col-rel (false ∷ true ∷ true ∷ []) (true ∷ true ∷ false ∷ []) (E1 false β))
                                               (back _ (sym fp)))
    where
    fp : place u (false ∷ true ∷ true ∷ []) (R β) ≈ col (false ∷ true ∷ true ∷ []) (Ex • R β • Ex)
    fp = trans (sym (trans left-unit right-unit)) (frame-1 (rig₃ β) ε u (sF 0F) pu Eq.refl (false ∷ true ∷ true ∷ []))

hgrot₀ : HGRot 0
hgrot₀ β u t pu s st 0F                  ()       jt sj
hgrot₀ β u t pu s st (sF 0F)             (s≤s ()) jt sj
hgrot₀ β u t pu s st (sF (sF (sF ())))   j≤       jt sj
hgrot₀ β u (sF (sF 0F)) pu s st (sF (sF 0F)) j≤ jt sj = ⊥-elim (jt Eq.refl)
hgrot₀ β u (sF (sF (sF ()))) pu s st (sF (sF 0F)) j≤ jt sj
hgrot₀ β u 0F pu (false ∷ _) () (sF (sF 0F)) j≤ jt sj
hgrot₀ β u 0F pu (true ∷ b ∷ false ∷ []) st (sF (sF 0F)) j≤ jt ()
hgrot₀ β u 0F pu (true ∷ b ∷ true ∷ []) st (sF (sF 0F)) j≤ jt sj = at₀ β u pu b
hgrot₀ β u (sF 0F) pu (a ∷ false ∷ _) () (sF (sF 0F)) j≤ jt sj
hgrot₀ β u (sF 0F) pu (a ∷ true ∷ false ∷ []) st (sF (sF 0F)) j≤ jt ()
hgrot₀ β u (sF 0F) pu (a ∷ true ∷ true ∷ []) st (sF (sF 0F)) j≤ jt sj = at₁ β u pu a
