/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: tests of the window step

The window step of `Weak` on windows placed by non-trivial swap networks,
on three and four wires.  Not imported by the development (the semantic
checks by `Sim.check` take a few minutes).
-/
import QCert.RealCliffordCH.Sec8.Weak

namespace QCert.RealCliffordCH.Sec8.WeakTest

open Circuit

/-! ## Tests of the window step on windows placed by swap networks -/

/-- The swap is an involution, on wires 0, 1 of three wires. -/
theorem swsw3 : Derivable (theory 3) (swAt 3 0 * swAt 3 0) 1 := by
  have h := derivable_rule Rule.g 1
  simpa [drawn, swAt, place2, map_mul] using h

/-- The swap is an involution, on wires 0, 1 and 1, 2 of four wires. -/
theorem swsw4 (j : ℕ) (hj : j < 2) : Derivable (theory 4) (swAt 4 j * swAt 4 j) 1 := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · have h := derivable_rule Rule.g 2
    simpa [drawn, swAt, place2, map_mul] using h
  · have h := derivable_shift (derivable_rule Rule.g 1)
    simpa [drawn, swAt, place2, map_mul] using h

/-- Two windows conjugated by the swap of wires 0, 1, each idle on wire 0
after the conjugation, are exchanged in one semantic step (semantics
decided on all three wires). -/
example (ih : IH 3) :
    Derivable (theory 3) (swAt 3 0 * shift cz * swAt 3 0 * (swAt 3 0 * shift (shift z) * swAt 3 0))
      (swAt 3 0 * shift (shift z) * swAt 3 0 * (swAt 3 0 * shift cz * swAt 3 0)) := by
  refine window ih (swAt 3 0) (swAt 3 0) swsw3 (a := cz * shift z) (b := shift z * cz) ?_ ?_
    (sem_of_check (by decide +kernel))
  · rw [map_mul]; exact conj_two swsw3
  · rw [map_mul]; exact conj_two swsw3

/-- On four wires, the network bringing wire 2 down to wire 0 (the swaps of
wires 1, 2 and 0, 1) and back: two `CZ`s placed by it commute, in one
semantic step (semantics decided one wire down). -/
example (ih : IH 4) :
    Derivable (theory 4)
      (swAt 4 1 * swAt 4 0 * shift cz * (swAt 4 0 * swAt 4 1) *
        (swAt 4 1 * swAt 4 0 * shift (shift cz) * (swAt 4 0 * swAt 4 1)))
      (swAt 4 1 * swAt 4 0 * shift (shift cz) * (swAt 4 0 * swAt 4 1) *
        (swAt 4 1 * swAt 4 0 * shift cz * (swAt 4 0 * swAt 4 1))) := by
  have h0 := swsw4 0 (by omega)
  have h1 := swsw4 1 (by omega)
  refine window' ih (swAt 4 1 * swAt 4 0) (swAt 4 0 * swAt 4 1) (inv_pair h0 h1)
    (a := cz * shift cz) (b := shift cz * cz) ?_ ?_ (sem_of_check (by decide +kernel))
  · rw [map_mul]; exact conj_two (inv_pair h1 h0)
  · rw [map_mul]; exact conj_two (inv_pair h1 h0)

end QCert.RealCliffordCH.Sec8.WeakTest
