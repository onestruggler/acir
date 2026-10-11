------------------------------------------------------------------------
-- Presentations of groups
--
-- The box on three qubits against its colourings, and as a squared
-- rotation (Clément, Appendix E.5 at n = 3, from Lemma D.2)
--
-- On three wires the box at the canonical position is CZ ↑ and the box
-- on wire 1 is CZ₂₀.  (335): CZ ↑ against a colouring of itself is a
-- two-wire evaluation one wire up, X on wire 0 not counting (`c335₀`).
-- (336): against CZ₂₀ and °CZ₂₀ it is Lemma D.2's CZ↑-CZ₂₀ and
-- CZ↑-°CZ₂₀, X on wire 1 not counting and X on wire 0 conjugating both
-- (`c336₀`).  (355): the box is the square of either rotation
-- (`core₀`, `core′₀`).  Only completeness on two qubits is used.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.Box
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (by-sem₀)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (CZ↑-CZ₂₀ ; CZ↑-°CZ₂₀ ; CCZX² ; CCXZ²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; B₁ ; C335 ; C336 ; col-flip ; X₁-B)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3)

open Tools (3 VRel,_===_)

private
  xb : X • Λ□ 2 ≈ Λ□ 2 • X
  xb = Canon.x-box canon3

  pass₃ : ∀ {a u v w : Circuit 3} → a • u ≈ u • a → a • v ≈ v • a → a • w ≈ w • a →
          a • (u • v • w) ≈ (u • v • w) • a
  pass₃ eu ev ew = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _
                     (trans (sym assoc) (trans (front _ ev) (trans assoc (trans (back _ ew) (sym assoc))))))
                     (sym assoc))))

  -- A white wire 0 is X on wire 0 around the black one.
  colX : ∀ (t : Bits 2) (w : Circuit 3) → col (false ∷ t) w ≈ X • col (true ∷ t) w • X
  colX t w = trans (back _ (back _ (X-↑ (negsB t))))
                   (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)

------------------------------------------------------------------------
-- (335)

private
  -- Two wires, one up.
  one : ∀ (t : Bits 2) → 2 ⊢ CZ • col t CZ ≈ col t CZ • CZ
  one (true  ∷ true  ∷ []) = by-sem₀ (CZ • col (true ∷ true ∷ []) CZ) (col (true ∷ true ∷ []) CZ • CZ) Eq.refl
  one (true  ∷ false ∷ []) = by-sem₀ (CZ • col (true ∷ false ∷ []) CZ) (col (true ∷ false ∷ []) CZ • CZ) Eq.refl
  one (false ∷ true  ∷ []) = by-sem₀ (CZ • col (false ∷ true ∷ []) CZ) (col (false ∷ true ∷ []) CZ • CZ) Eq.refl
  one (false ∷ false ∷ []) = by-sem₀ (CZ • col (false ∷ false ∷ []) CZ) (col (false ∷ false ∷ []) CZ • CZ) Eq.refl

c335₀ : C335 0
c335₀ (true ∷ t)  = c335t t
  where
  c335t : ∀ t → Λ□ 2 • col (true ∷ t) (Λ□ 2) ≈ col (true ∷ t) (Λ□ 2) • Λ□ 2
  c335t t = lemma-cong↑ (CZ • col t CZ) (col t CZ • CZ) (one t)
c335₀ (false ∷ t) = trans (back _ e) (trans t′ (front _ (sym e)))
  where
  e : col (false ∷ t) (Λ□ 2) ≈ col (true ∷ t) (Λ□ 2)
  e = col-flip 0F (true ∷ t) xb
  t′ : Λ□ 2 • col (true ∷ t) (Λ□ 2) ≈ col (true ∷ t) (Λ□ 2) • Λ□ 2
  t′ = lemma-cong↑ (CZ • col t CZ) (col t CZ • CZ) (one t)

------------------------------------------------------------------------
-- (336)

private
  -- Black on the wires 0 1.
  c336T : ∀ c → Λ□ 2 • col (true ∷ true ∷ c ∷ []) (B₁ 0) ≈ col (true ∷ true ∷ c ∷ []) (B₁ 0) • Λ□ 2
  c336T true  = trans (back _ (trans left-unit right-unit)) (trans CZ↑-CZ₂₀ (front _ (sym (trans left-unit right-unit))))
  c336T false = trans (back _ e) (trans CZ↑-°CZ₂₀ (front _ (sym e)))
    where
    e : col (true ∷ true ∷ false ∷ []) (B₁ 0) ≈ X ↑ ↑ • CZ₂₀ • X ↑ ↑
    e = cong right-unit (back _ right-unit)

  -- Black on wire 0: X on wire 1 does not count.
  c336t : ∀ b c → Λ□ 2 • col (true ∷ b ∷ c ∷ []) (B₁ 0) ≈ col (true ∷ b ∷ c ∷ []) (B₁ 0) • Λ□ 2
  c336t true  c = c336T c
  c336t false c = trans (back _ e) (trans (c336T c) (front _ (sym e)))
    where
    e : col (true ∷ false ∷ c ∷ []) (B₁ 0) ≈ col (true ∷ true ∷ c ∷ []) (B₁ 0)
    e = col-flip (sF 0F) (true ∷ true ∷ c ∷ []) (X₁-B xb)

c336₀ : C336 0
c336₀ (true  ∷ b ∷ c ∷ []) = c336t b c
c336₀ (false ∷ b ∷ c ∷ []) =
  trans (back _ (colX t (B₁ 0)))
        (trans (pass₃ (sym (X-↑ CZ)) (c336t b c) (sym (X-↑ CZ))) (front _ (sym (colX t (B₁ 0)))))
  where
  t : Bits 2
  t = b ∷ c ∷ []

------------------------------------------------------------------------
-- (355): the box squared from either rotation

core₀ : Λ□ 2 ≈ ΛXZ 2 • ΛXZ 2
core₀ = sym CCXZ²

core′₀ : Λ□ 2 ≈ ΛZX 2 • ΛZX 2
core′₀ = sym CCZX²
