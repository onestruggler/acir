/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations in the theory of Figure 6

Words are lists of generators (`FreeMonoid.ofList`).  `rw_at w k h` rewrites
the segment of `w` starting at position `k` by a derivation `h : L ≈ R`; a
derivation is a chain of such rewrites, each checked by `rfl` on lists with
symbolic indices.  The relations of Figure 6 are restated on lists
(`r_a1`, …), together with the derived relations (e1)/(e2) in the form we
use (`conj` lemmas) and (f1).
-/
import QCert.HadamardPi.Soundness

namespace QCert.HadamardPi

open FreeMonoid

variable {n : ℕ}

section General

variable {X : Type*} {Γ : WRel X}

/-- Rewrite the segment at position `k`. -/
theorem rw_at (w : List X) (k : ℕ) {L R : List X} (h : Derivable Γ (ofList L) (ofList R))
    (hm : (w.drop k).take L.length = L) :
    Derivable Γ (ofList w) (ofList (w.take k ++ R ++ w.drop (k + L.length))) := by
  have hw : w = w.take k ++ L ++ w.drop (k + L.length) := by
    conv_lhs => rw [← List.take_append_drop k w, ← List.take_append_drop L.length (w.drop k)]
    rw [hm, List.drop_drop, List.append_assoc]
  conv_lhs => rw [hw]
  simp only [ofList_append]
  exact ((Derivable.refl _).mul h).mul (Derivable.refl _)

theorem der_symm {L R : List X} (h : Derivable Γ (ofList L) (ofList R)) :
    Derivable Γ (ofList R) (ofList L) := h.symm

/-- `u x u ≈ y` from `x u ≈ u y` and `u u ≈ ε`. -/
theorem conj_l {u x y : Word X} (h : Derivable Γ (x * u) (u * y)) (hu : Derivable Γ (u * u) 1) :
    Derivable Γ (u * x * u) y := by
  have h1 : Derivable Γ (u * x * u) (u * u * y) := by
    rw [mul_assoc, mul_assoc]; exact (Derivable.refl u).mul h
  exact h1.trans (by simpa using hu.mul (Derivable.refl y))

/-- `u x u ≈ y` from `y u ≈ u x` and `u u ≈ ε`. -/
theorem conj_r {u x y : Word X} (h : Derivable Γ (y * u) (u * x)) (hu : Derivable Γ (u * u) 1) :
    Derivable Γ (u * x * u) y := by
  have h1 : Derivable Γ (u * x * u) (y * u * u) := (h.symm).mul (Derivable.refl u)
  exact h1.trans (by rw [mul_assoc]; simpa using (Derivable.refl y).mul hu)

end General

end QCert.HadamardPi
