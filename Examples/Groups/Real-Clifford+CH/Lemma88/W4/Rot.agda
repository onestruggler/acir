------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations on four qubits against each other and against the box
-- (Clément, Appendix E.5 at n = 4, from Lemma D.5)
--
-- On four wires the rotations are ZX₃ and XZ₃, and the facts the
-- placement modules (RotAnywhereGen, BraidFrom, PairFrom) need come from
-- Lemma D.5:
--
-- * (351), the rotation against a colouring of a rotation white on wire
--   1: under the swap of the wires 1 2, which fixes the rotations
--   ((215)), it is white on wire 2, and that is (241) (GeneralN.Colours'
--   norm-ZX; X on the target turns the rotation over, (238)).
-- * (352), crossed targets: (240) (norm-K).
-- * (356): (238).  (357): ThreeQubit's argument for K-W one wire up —
--   the lower CZ conjugates CH to Z CH Z and fixes the box on wire 1
--   ((160)), and Z on the target exchanges the rotations ((237)).
-- * (358): Canon358Gen, with the merge over the wires 2 3 (MergeKit
--   over W4.Kit's top merges) and RotComm 1.
-- * The pair step: black by definition, white on wire 0 because there
--   the box on wire 1 is the box times CZ ↑ ↑ (the merge on wire 1), which
--   the rotations pass.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Rot
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; X² ; Z² ; CZ²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁ ; module S₁₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq160 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃ using (eq237)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (eq241 ; C₂₄₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ using (eq240 ; D₂₄₀)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; swapAt-negsB ; negs-flip ; negs-flip′ ; X-negs)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (combine ; _⇔_)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (col-rel ; combine-lookup)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; col-flip ; X₁-B)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (norm-ZX ; norm-K ; N₀-rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq270)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol
  using (rot ; RotComm ; C351 ; C352 ; PairCanon ; PairStep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (Braid ; E356 ; E358)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Kit complete₂ complete₃ using (s12₄ ; rig₄ ; tm₄)
import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhereGen as RotAnywhereGen
import Examples.Groups.Real-Clifford+CH.GeneralN.BraidFrom as BraidFrom
import Examples.Groups.Real-Clifford+CH.GeneralN.PairFrom as PairFrom
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon358Gen as Canon358Gen
import Examples.Groups.Real-Clifford+CH.Lemma88.MergeKit as MergeKit

open Tools (4 VRel,_===_)
open WordAlgebra (4 VRel,_===_) using (comm-abab)

private
  R : Bool → Circuit 4
  R = rot {1}

  B : Circuit 4
  B = Ex ↓ • Λ□ 3 • Ex ↓

  pass₂ : ∀ {a u v : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  -- A colouring of a gate conjugated by X on wire i is the colouring
  -- flipped there.
  col-N : ∀ (i : Fin 4) (s : Bits 4) (w : Circuit 4) →
          col s (Xat (toℕ i) • w • Xat (toℕ i)) ≈ col (flipAt (toℕ i) s) w
  col-N i s w = sym (begin
    negsB (flipAt (toℕ i) s) • w • negsB (flipAt (toℕ i) s)
      ≈⟨ cong (negs-flip′ i s) (back _ (negs-flip i s)) ⟩
    (negsB s • Xat (toℕ i)) • w • (Xat (toℕ i) • negsB s)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    negsB s • (Xat (toℕ i) • w • Xat (toℕ i)) • negsB s ∎)

  -- X on the target turns the rotation over ((238)).
  X-ZX : X • R true • X ≈ R false
  X-ZX = N₀-rot false

------------------------------------------------------------------------
-- (351)

private
  S₁₂R : ∀ β → S₁₂.⟪ R β ⟫ ≈ R β
  S₁₂R β = S₁₂.⟪⟫-fix (s12₄ β)

  -- The rotation coloured black on wire 0, white on wire 2.
  colR : ∀ b d β → col (true ∷ b ∷ false ∷ d ∷ []) (R β) ≈ C₂₄₁ d b β
  colR b d true  = norm-ZX true b d []
  colR b d false = trans (back _ (front _ (sym X-ZX))) (trans (col-N 0F (true ∷ b ∷ false ∷ d ∷ []) (R true))
                                                              (norm-ZX false b d []))

  sep₂ : ∀ α β b d → R α • col (true ∷ b ∷ false ∷ d ∷ []) (R β) ≈ col (true ∷ b ∷ false ∷ d ∷ []) (R β) • R α
  sep₂ true  β b d = trans (back _ (colR b d β)) (trans (eq241 true true d b true β) (front _ (sym (colR b d β))))
  sep₂ false β b d = trans (back _ (colR b d β)) (trans (eq241 true true d b false β) (front _ (sym (colR b d β))))

  c351z : ∀ α β (z : Bits 4) → lookupℕ 0 z ≡ true → lookupℕ 1 z ≡ false →
          R α • col z (R β) ≈ col z (R β) • R α
  c351z α β (true ∷ false ∷ z₂ ∷ z₃ ∷ []) _ _ =
    S₁₂.⟪⟫-≈ (sep₂ α β z₂ z₃) (S₁₂.⟪⟫-•₂ (S₁₂R α) cS) (S₁₂.⟪⟫-•₂ cS (S₁₂R α))
    where
    cS : S₁₂.⟪ col (true ∷ z₂ ∷ false ∷ z₃ ∷ []) (R β) ⟫ ≈ col (true ∷ false ∷ z₂ ∷ z₃ ∷ []) (R β)
    cS = trans (S₁₂.⟪⟫-•₃ (swapAt-negsB 1 (true ∷ z₂ ∷ false ∷ z₃ ∷ [])) refl
                           (swapAt-negsB 1 (true ∷ z₂ ∷ false ∷ z₃ ∷ [])))
               (mid _ _ (S₁₂R β))
  c351z α β (false ∷ _)       () _
  c351z α β (true ∷ true ∷ _) _  ()

c351₁ : C351 1
c351₁ α β x y x0 y0 d = col-rel x y (c351z α β (combine x y) z0 z1)
  where
  z0 : lookupℕ 0 (combine x y) ≡ true
  z0 = Eq.trans (combine-lookup 0 x y (s≤s z≤n)) (Eq.cong₂ _⇔_ x0 y0)
  z1 : lookupℕ 1 (combine x y) ≡ false
  z1 = Eq.trans (combine-lookup 1 x y (s≤s (s≤s z≤n))) d

------------------------------------------------------------------------
-- (352)

private
  -- The rotation on wire 1.
  K₁ : Circuit 4
  K₁ = S₀₁.⟪ R true ⟫

  S₀₁X : S₀₁.⟪ X ⟫ ≈ X ↑
  S₀₁X = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  -- XZ on wire 1 is ZX on wire 1 conjugated by X on wire 1.
  K-flip : S₀₁.⟪ R false ⟫ ≈ X ↑ • K₁ • X ↑
  K-flip = trans (S₀₁.⟪⟫-cong (sym X-ZX)) (S₀₁.⟪⟫-•₃ S₀₁X refl S₀₁X)

  colK : ∀ a b d β → col (a ∷ b ∷ false ∷ d ∷ []) (S₀₁.⟪ R β ⟫) ≈ D₂₄₀ d a (b ⇔ β)
  colK a true  d true  = norm-K a true d []
  colK a false d true  = norm-K a false d []
  colK a true  d false = trans (back _ (front _ K-flip)) (trans (col-N (sF 0F) (a ∷ true ∷ false ∷ d ∷ []) K₁)
                                                                (norm-K a false d []))
  colK a false d false = trans (back _ (front _ K-flip)) (trans (col-N (sF 0F) (a ∷ false ∷ false ∷ d ∷ []) K₁)
                                                                (norm-K a true d []))

  c352z : ∀ α β (z : Bits 4) → lookupℕ 2 z ≡ false →
          R α • col z (Ex • R β • Ex) ≈ col z (Ex • R β • Ex) • R α
  c352z true  β (z₀ ∷ z₁ ∷ false ∷ z₃ ∷ []) _ =
    trans (back _ (colK z₀ z₁ z₃ β)) (trans (eq240 true true z₃ z₀ true (z₁ ⇔ β)) (front _ (sym (colK z₀ z₁ z₃ β))))
  c352z false β (z₀ ∷ z₁ ∷ false ∷ z₃ ∷ []) _ =
    trans (back _ (colK z₀ z₁ z₃ β)) (trans (eq240 true true z₃ z₀ false (z₁ ⇔ β)) (front _ (sym (colK z₀ z₁ z₃ β))))
  c352z α β (z₀ ∷ z₁ ∷ true ∷ z₃ ∷ []) ()

c352₁ : C352 1
c352₁ α β x y x0 y1 d = col-rel x y (c352z α β (combine x y) z2)
  where
  z2 : lookupℕ 2 (combine x y) ≡ false
  z2 = Eq.trans (combine-lookup 2 x y (s≤s (s≤s (s≤s z≤n)))) d

rotcomm₁ : RotComm 1
rotcomm₁ = RotAnywhereGen.rot-comm rig₄ c351₁ c352₁

------------------------------------------------------------------------
-- (356), (357), (358)

e356₁ : E356 1
e356₁ = conj-sym X² X-ZX

private
  module K = Conj {4} (CZ ↓) CZ²
  module Zc = Conj {4} (Z ↓) Z²

  a′ : Circuit 4
  a′ = Z ↓ • CH • Z ↓

  B² : B • B ≈ ε
  B² = trans (sym (S₀₁.⟪⟫-• (Λ□ 3) (Λ□ 3))) (trans (S₀₁.⟪⟫-cong eq166) S₀₁.⟪⟫-ε)

  K-a : K.⟪ CH ↓ ⟫ ≈ a′
  K-a = L-sem (CZ • CH • CZ) (Z ↓ • CH • Z ↓) Eq.refl

  K-b : K.⟪ B ⟫ ≈ B
  K-b = K.⟪⟫-fix (S₀₁.⟪⟫-≈ eq160 (S₀₁.⟪⟫-•₂ sCZ refl) (S₀₁.⟪⟫-•₂ refl sCZ))
    where
    sCZ : S₀₁.⟪ CZ ↓ ⟫ ≈ CZ ↓
    sCZ = L-sem (Ex • CZ • Ex) CZ Eq.refl

  Zc-b : Zc.⟪ B ⟫ ≈ B
  Zc-b = Zc.⟪⟫-fix (S₀₁.⟪⟫-≈ (eq270 3 0F) (S₀₁.⟪⟫-•₂ sZ refl) (S₀₁.⟪⟫-•₂ refl sZ))
    where
    sZ : S₀₁.⟪ Z ↑ ⟫ ≈ Z ↓
    sZ = L-sem (Ex • Z ↑ • Ex) Z Eq.refl

  Zc-V : Zc.⟪ R false ⟫ ≈ R true
  Zc-V = trans (sym assoc) (trans (front _ eq237) (trans assoc (trans (back _ Z²) right-unit)))

  star : B • a′ • B • a′ ≈ R true
  star = trans (sym (Zc.⟪⟫-•₄ Zc-b refl Zc-b refl)) Zc-V

  star′ : a′ • B • a′ • B ≈ R false
  star′ = begin
    a′ • B • a′ • B
      ≈⟨ sym (trans (sym assoc) (trans (front _ B²) left-unit)) ⟩
    B • B • a′ • B • a′ • B
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • (□ • □ • □ • □) • □) Eq.refl ⟩
    B • (B • a′ • B • a′) • B
      ≈⟨ back _ (front _ star) ⟩
    B • (CH • B • CH • B) • B
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) ((□ • □ • □ • □) • (□ • □)) Eq.refl ⟩
    (B • CH • B • CH) • (B • B)
      ≈⟨ trans (back _ B²) right-unit ⟩
    R false ∎

  e357₁ : CZ ↓ • R true • CZ ↓ ≈ R false
  e357₁ = trans (K.⟪⟫-•₄ K-a K-b K-a K-b) star′

e358₁ : E358 1
e358₁ = Canon358Gen.eq358 canon4 complete₂ rotcomm₁ (λ β → MergeKit.merge₁R {1} tm₄ β 2 ≤-refl) e357₁

braid₁ : Braid 1
braid₁ = BraidFrom.braid rig₄ e356₁ e358₁

------------------------------------------------------------------------
-- The pair step

private
  M : Circuit 4
  M = CZ ↑ ↑

  xb : X • Λ□ 3 ≈ Λ□ 3 • X
  xb = Canon.x-box canon4

  module N₁ = Conj {4} (X ↑) (lemma-cong↑ (X • X) ε X²)

  -- The merge on wire 1, in both orders: the box passes M.
  m₁ : Λ□ 3 • N₁.⟪ Λ□ 3 ⟫ ≈ M
  m₁ = Canon.merge canon4

  m₁′ : N₁.⟪ Λ□ 3 ⟫ • Λ□ 3 ≈ M
  m₁′ = N₁.⟪⟫-≈ m₁ (N₁.⟪⟫-•₂ refl (N₁.⟪⟫-⟪⟫ (Λ□ 3)))
                   (N₁.⟪⟫-fix (lemma-cong↑ (X • CZ ↑) (CZ ↑ • X) (X-↑ CZ)))

  Λ² : Λ□ 3 • Λ□ 3 ≈ ε
  Λ² = Canon.invol canon4

  M-Λ : M • Λ□ 3 ≈ Λ□ 3 • M
  M-Λ = begin
    M • Λ□ 3                          ≈⟨ front _ (sym m₁′) ⟩
    (N₁.⟪ Λ□ 3 ⟫ • Λ□ 3) • Λ□ 3       ≈⟨ trans assoc (trans (back _ Λ²) right-unit) ⟩
    N₁.⟪ Λ□ 3 ⟫                       ≈⟨ sym (trans (sym assoc) (trans (front _ Λ²) left-unit)) ⟩
    Λ□ 3 • (Λ□ 3 • N₁.⟪ Λ□ 3 ⟫)       ≈⟨ back _ m₁ ⟩
    Λ□ 3 • M ∎

  M-B : M • B ≈ B • M
  M-B = S₀₁.⟪⟫-≈ M-Λ (S₀₁.⟪⟫-•₂ sM refl) (S₀₁.⟪⟫-•₂ refl sM)
    where
    sM : S₀₁.⟪ M ⟫ ≈ M
    sM = S₀₁.⟪⟫-fix (low-comm Ex CZ)

  R-M : ∀ γ → R γ • M ≈ M • R γ
  R-M true  = sym (comm-abab (sym (low-comm CH CZ)) M-B)
  R-M false = sym (comm-abab M-B (sym (low-comm CH CZ)))

  -- Black: by definition.
  k1b : ∀ β → R β • B ≈ B • R (not β)
  k1b false = by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl
  k1b true  = begin
    (CH • B • CH • B) • B      ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    CH • B • CH • (B • B)      ≈⟨ back _ (back _ (trans (back _ B²) right-unit)) ⟩
    CH • B • CH                ≈⟨ sym (trans (sym assoc) (trans (front _ B²) left-unit)) ⟩
    B • (B • CH • B • CH) ∎

  -- White on wire 0: X B X is B M, the merge on wire 1 under the lower
  -- swap.
  S₀₁X₁ : S₀₁.⟪ X ↑ ⟫ ≈ X
  S₀₁X₁ = L-sem (Ex • X ↑ • Ex) X Eq.refl

  mergeS : B • (X • B • X) ≈ M
  mergeS = S₀₁.⟪⟫-≈ m₁ (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-•₃ S₀₁X₁ refl S₀₁X₁)) (S₀₁.⟪⟫-fix (low-comm Ex CZ))

  XBX : X • B • X ≈ B • M
  XBX = begin
    X • B • X                 ≈⟨ sym left-unit ⟩
    ε • (X • B • X)           ≈⟨ front _ (sym B²) ⟩
    (B • B) • (X • B • X)     ≈⟨ trans assoc (back _ mergeS) ⟩
    B • M ∎

  k1w : ∀ β → R β • (X • B • X) ≈ (X • B • X) • R (not β)
  k1w β = trans (back _ XBX) (trans (sym assoc) (trans (front _ (k1b β)) (trans assoc
            (trans (back _ (R-M (not β))) (trans (sym assoc) (front _ (sym XBX)))))))

  k1t : ∀ β γ → R β • col (γ ∷ true ∷ true ∷ true ∷ []) B ≈ col (γ ∷ true ∷ true ∷ true ∷ []) B • R (not β)
  k1t β true  = trans (back _ u) (trans (k1b β) (front _ (sym u)))
    where
    u : col (true ∷ true ∷ true ∷ true ∷ []) B ≈ B
    u = trans left-unit right-unit
  k1t β false = trans (back _ u) (trans (k1w β) (front _ (sym u)))
    where
    u : col (false ∷ true ∷ true ∷ true ∷ []) B ≈ X • B • X
    u = cong right-unit (back _ right-unit)

k1₁ : PairCanon 1
k1₁ β γ true  = k1t β γ
k1₁ β γ false = trans (back _ e) (trans (k1t β γ) (front _ (sym e)))
  where
  e : col (γ ∷ false ∷ true ∷ true ∷ []) B ≈ col (γ ∷ true ∷ true ∷ true ∷ []) B
  e = col-flip (sF 0F) (γ ∷ true ∷ true ∷ true ∷ []) (X₁-B xb)

pairstep₁ : PairStep 1
pairstep₁ = PairFrom.pair-step (Canon.swaps canon4) rig₄ k1₁
