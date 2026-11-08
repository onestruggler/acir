------------------------------------------------------------------------
-- Two-sided inverses, using only derivations in the circuit theory.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Invertible where

open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Presentation.Base _===_ hiding (_===_ ; _≈_)
open import Presentation.Properties _===_ using (word-setoid ; by-assoc)
import Presentation.Properties as PP
open PP.Pattern-Assoc _===_ using (□ ; by-passoc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Binary.Reasoning.Setoid word-setoid

record Invertible (w : Word Gen) : Set where
  constructor invertible
  field
    inverse : Word Gen
    left : inverse • w ≈ ε
    right : w • inverse ≈ ε

invol : ∀ {w} → w • w ≈ ε → Invertible w
invol {w} e = invertible w e e

along : ∀ {w v} → w ≈ v → Invertible v → Invertible w
along e (invertible i l r) =
  invertible i (trans (cong refl e) l) (trans (cong e refl) r)

product : ∀ {w v} → Invertible w → Invertible v → Invertible (w • v)
product {w} {v} (invertible i li ri) (invertible j lj rj) =
  invertible (j • i)
    (begin
      (j • i) • (w • v) ≈⟨ by-passoc
        ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) Eq.refl ⟩
      j • ((i • w) • v) ≈⟨ cong refl (cong li refl) ⟩
      j • (ε • v)       ≈⟨ cong refl left-unit ⟩
      j • v             ≈⟨ lj ⟩
      ε                 ∎)
    (begin
      (w • v) • (j • i) ≈⟨ by-passoc
        ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) Eq.refl ⟩
      w • ((v • j) • i) ≈⟨ cong refl (cong rj refl) ⟩
      w • (ε • i)       ≈⟨ cong refl left-unit ⟩
      w • i             ≈⟨ ri ⟩
      ε                 ∎)

-- If the outer factors and their product with b are invertible,
-- the middle factor b is invertible too. No cancellation assumption
-- on the whole presented monoid is used here.
middle : ∀ {a b c} → Invertible a → Invertible c →
         Invertible (a • b • c) → Invertible b
middle {a} {b} {c} (invertible ia la ra) (invertible ic lc rc)
  (invertible i l r) = invertible (c • i • a)
    (begin
      (c • i • a) • b         ≈⟨ by-passoc
        ((□ • □ • □) • □) (□ • ((□ • (□ • □)) • ε)) Eq.refl ⟩
      c • ((i • (a • b)) • ε) ≈⟨ cong refl (cong refl (sym rc)) ⟩
      c • ((i • (a • b)) • (c • ic)) ≈⟨ by-passoc
        (□ • ((□ • (□ • □)) • (□ • □)))
        (□ • ((□ • (□ • □ • □)) • □)) Eq.refl ⟩
      c • ((i • (a • b • c)) • ic) ≈⟨ cong refl (cong l refl) ⟩
      c • (ε • ic)           ≈⟨ cong refl left-unit ⟩
      c • ic                 ≈⟨ rc ⟩
      ε                      ∎)
    (begin
      b • (c • i • a)         ≈⟨ sym left-unit ⟩
      ε • (b • c • i • a)     ≈⟨ cong (sym la) refl ⟩
      (ia • a) • (b • c • i • a) ≈⟨ by-passoc
        ((□ • □) • (□ • □ • □ • □))
        (□ • (((□ • □ • □) • □) • □)) Eq.refl ⟩
      ia • (((a • b • c) • i) • a) ≈⟨ cong refl (cong r refl) ⟩
      ia • (ε • a)           ≈⟨ cong refl left-unit ⟩
      ia • a                 ≈⟨ la ⟩
      ε                      ∎)
