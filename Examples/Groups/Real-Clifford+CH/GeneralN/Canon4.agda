------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical box facts and the merge (309) on four qubits
--
-- The frames of Lemmas 8.4 and 8.7 need, at each width, six facts about
-- the box (BoxFrames' `Canon`) and the merge (309) of a black and a
-- white control on every control wire.  On four qubits they are
-- Lemma D.5: the involution (166); X on the box wire by (154) and (155);
-- the symmetry in the controls (BoxSym's `sym-0`, from (157) and (161));
-- the merge (170) on wire 2, carried to wire 1 by the swap of the wires
-- 1, 2 and taken on wire 3 from (170) under the swap of 2, 3.  The one
-- fact Lemma D.5 does not state is the case x = y of (336), that the box
-- commutes with the box whose box wire is wire 1 (`comm-B′`): by (170)
-- the box is the box negated on wire 2 times the CZ of the wires 1, 3,
-- and the box on wire 1 passes both, the first by (179), the second
-- because under the swap of the wires 0, 1 it is the CZ from wire 3 to
-- the box wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon4
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; P₂₃ ; P₁₃ ; P₀₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq154 ; eq155 ; eq157 ; eq166 ; CZ₃₀-box)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃ using (°box₃ ; eq170 ; eq170′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (eq179 ; module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃ using (eq170₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ using (box₃′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (swapX)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (on2 ; placeAt-on2-hi ; placeAt-on2-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (sym-net ; sym-0)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.WordAlgebra (4 VRel,_===_) using (inv-unique ; unwrap′ ; comm-•)

private
  -- X across the swap, three wires.
  e₃ : 3 ⊢ Ex • X ↑ • Ex ≈ X
  e₃ = trans (back _ swapX) (trans (sym assoc) (trans (front _ Ex²) left-unit))
    where open Tools (3 VRel,_===_)

open Tools (4 VRel,_===_)

private
  B B′ °B : Circuit 4
  B  = box₃ {0}
  B′ = box₃′ {0}
  °B = °box₃ {0}

  CZ↑↑² : CZ ↑ ↑ • CZ ↑ ↑ ≈ ε
  CZ↑↑² = lemma-cong↑ (CZ ↑ • CZ ↑) ε (lemma-cong↑ (CZ • CZ) ε CZ²)

  CZ↑² : CZ ↑ • CZ ↑ ≈ ε
  CZ↑² = lemma-cong↑ (CZ • CZ) ε CZ²

  -- The swap of the wires 0, 1 passes the CZ of the wires 2, 3.
  wire : Ex • CZ ↑ ↑ • Ex ≈ CZ ↑ ↑
  wire = trans (sym assoc) (trans (front _ (low-comm Ex CZ)) (trans assoc (trans (back _ Ex²) right-unit)))

  -- (170) on wire 1: the swap of the wires 1, 2 carries it there.
  merge₁ : B • (X ↑ • B • X ↑) ≈ CZ ↑ ↑
  merge₁ = S₁₂.⟪⟫-≈ (eq170 {0}) (S₁₂.⟪⟫-•₂ (eq157 {0}) (S₁₂.⟪⟫-•₃ sX (eq157 {0}) sX)) (S₁₂.⟪⟫-⟪⟫ (P₂₃ CZ))
    where
    sX : S₁₂.⟪ X ↑ ↑ ⟫ ≈ X ↑
    sX = lemma-cong↑ (Ex • X ↑ • Ex) X e₃

  -- The box on wire 1 passes the CZ of the wires 1, 3.
  B′-d : B′ • P₁₃ CZ ≈ P₁₃ CZ • B′
  B′-d = sym (S₀₁.⟪⟫-≈ (CZ₃₀-box {0}) (S₀₁.⟪⟫-•₂ c↦d refl) (S₀₁.⟪⟫-•₂ refl c↦d))
    where
    c↦d : S₀₁.⟪ CZ₃₀ ⟫ ≈ P₁₃ CZ
    c↦d = trans (S₀₁.⟪⟫-cong CZ₃₀-P) (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ))

  -- The box is the box negated on wire 2 times the CZ of the wires 1, 3.
  B-form : B ≈ °B • P₁₃ CZ
  B-form = begin
    B                   ≈⟨ sym left-unit ⟩
    ε • B               ≈⟨ front _ (sym (N₂.⟪⟫-invol (eq166 {0}))) ⟩
    (°B • °B) • B       ≈⟨ assoc ⟩
    °B • (°B • B)       ≈⟨ back _ (eq170′ {0}) ⟩
    °B • P₁₃ CZ ∎

-- The case x = y of (336).
comm-B′ : B • B′ ≈ B′ • B
comm-B′ = begin
  B • B′                    ≈⟨ front _ B-form ⟩
  (°B • P₁₃ CZ) • B′        ≈⟨ assoc ⟩
  °B • (P₁₃ CZ • B′)        ≈⟨ back _ (sym B′-d) ⟩
  °B • (B′ • P₁₃ CZ)        ≈⟨ sym assoc ⟩
  (°B • B′) • P₁₃ CZ        ≈⟨ front _ (sym (eq179 {0})) ⟩
  (B′ • °B) • P₁₃ CZ        ≈⟨ assoc ⟩
  B′ • (°B • P₁₃ CZ)        ≈⟨ back _ (sym B-form) ⟩
  B′ • B ∎

canon4 : Canon 1
canon4 = record
  { invol   = eq166 {0}
  ; x-box   = sym (comm-• (sym (eq155 {0})) (comm-• (sym (eq154 {0})) (sym (eq155 {0}))))
  ; swaps   = sym-net 0 sym-0
  ; merge   = merge₁
  ; wire274 = wire
  ; comm336 = comm-B′
  }

------------------------------------------------------------------------
-- (309) on each control wire, the negated box first

private
  -- A conjugated box times the box is what the box times it is.
  order-flip : ∀ {M d : Circuit 4} → M • M ≈ ε → d • d ≈ ε → B • M ≈ d → M • B ≈ d
  order-flip MM dd e = inv-unique (unwrap′ MM (eq166 {0})) dd e

  place2 : placeAt 2 (Λ□ 2) ≈ P₁₃ CZ
  place2 = begin
    ((ε • Ex ↑) • Ex) • CZ ↑ ↑ • (Ex • (Ex ↑ • ε))
      ≈⟨ cong (front _ left-unit) (back _ (back _ right-unit)) ⟩
    (Ex ↑ • Ex) • CZ ↑ ↑ • (Ex • Ex ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    Ex ↑ • (Ex • CZ ↑ ↑ • Ex) • Ex ↑
      ≈⟨ back _ (front _ wire) ⟩
    Ex ↑ • CZ ↑ ↑ • Ex ↑ ∎

merge4 : ∀ c → 1 ≤ c → c ≤ 3 → (Xat c • Λ□ 3 • Xat c) • Λ□ 3 ≈ placeAt c (Λ□ 2)
merge4 zero                ()      _
merge4 (suc zero)          _       _ =
  trans (order-flip (N₁.⟪⟫-invol (eq166 {0})) CZ↑↑² merge₁)
        (sym (placeAt-on2-hi CZ 1 1 ≤-refl (s≤s z≤n)))
merge4 (suc (suc zero))    _       _ = trans (eq170′ {0}) (sym place2)
merge4 (suc (suc (suc zero))) _    _ =
  trans (order-flip (N₃.⟪⟫-invol (eq166 {0})) CZ↑² (eq170₃ {0}))
        (sym (placeAt-on2-top CZ 1 (s≤s (s≤s (s≤s z≤n)))))
merge4 (suc (suc (suc (suc c)))) _ (s≤s (s≤s (s≤s ())))
