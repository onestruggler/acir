/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Every gate is invertible in the theory

`H`, `Z`, `CZ` and `CH` are involutions by Equations (1), (2), (4) and (5),
on the bottom wires of every circuit, and a gate moved up is inverted by its
inverse moved up (`derivable_shift`).
-/
import QCert.RealCliffordCH.Syntax

namespace QCert.RealCliffordCH

open Circuit

/-- A derivation moved up one wire. -/
theorem derivable_shift {R : CRel Gate} {n : ℕ} {a b : Circ n}
    (h : Derivable (Lift R n) a b) : Derivable (Lift R (n + 1)) (shift a) (shift b) := by
  let c : Con (Circ n) := (conGen (Lift R (n + 1))).comap shift (map_mul shift)
  have hc : conGen (Lift R n) ≤ c :=
    Con.conGen_le fun x y hxy => ConGen.Rel.of _ _ (Lift.shift hxy)
  exact hc h

/-- A rule on the bottom wires of a wider circuit. -/
theorem derivable_rule {k : ℕ} {w v : Circ k} (r : Rule k w v) (m : ℕ) :
    Derivable (theory (m + k)) (pad m w) (pad m v) :=
  Derivable.of (Lift.rule (Padded.pad m r))

/-- Every generator has an inverse modulo the theory: itself. -/
theorem grouplike (n : ℕ) : Grouplike (theory n) := by
  intro x
  induction x with
  | gate0 c => exact nomatch c
  | @gate1 m g =>
    refine ⟨FreeMonoid.of (Gen.gate1 g), ?_⟩
    cases g
    · exact derivable_rule Rule.e1 m
    · exact derivable_rule Rule.e2 m
  | @gate2 m g =>
    refine ⟨FreeMonoid.of (Gen.gate2 g), ?_⟩
    cases g
    · exact derivable_rule Rule.e4 m
    · exact derivable_rule Rule.e5 m
  | gate3 c => exact nomatch c
  | @up m g ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨shift w, ?_⟩
    simpa [map_mul] using derivable_shift hw

end QCert.RealCliffordCH
