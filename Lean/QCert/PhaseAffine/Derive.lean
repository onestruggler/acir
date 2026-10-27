/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations in a lifted rule set

General tools for the theories `Lift (Padded Base)` of the framework:
a derivation moved up one wire (`derivable_shift`) or onto the bottom
wires of a wider circuit (`derivable_pad`), and a rule of `Base` applied on
the bottom wires (`Derivable.base`).
-/
import QCert.Circuit.Basic

namespace QCert

variable {Gate : ℕ → Type}

/-- A derivation moved up one wire. -/
theorem derivable_shift {R : CRel Gate} {n : ℕ} {w v : Circuit Gate n}
    (h : Derivable (Lift R n) w v) :
    Derivable (Lift R (n + 1)) (Circuit.shift w) (Circuit.shift v) := by
  have : conGen (Lift R n) ≤
      Con.comap Circuit.shift (fun x y => map_mul Circuit.shift x y) (conGen (Lift R (n + 1))) :=
    Con.conGen_le fun x y hr => ConGen.Rel.of _ _ (Lift.shift hr)
  exact this h

/-- A rule of the base set on the bottom wires of `n + k` wires. -/
theorem Derivable.base {Base : CRel Gate} {k : ℕ} (n : ℕ) {w v : Circuit Gate k}
    (h : Base k w v) :
    Derivable (Lift (Padded Base) (n + k)) (Circuit.pad n w) (Circuit.pad n v) :=
  Derivable.of (Lift.rule (Padded.pad n h))

theorem Circuit.pad_g0 (n : ℕ) {k : ℕ} (g : Gate 0) :
    Circuit.pad n (Circuit.g0 (n := k) g) = Circuit.g0 g := rfl

theorem Circuit.pad_g1 (n : ℕ) {k : ℕ} (g : Gate 1) :
    Circuit.pad n (Circuit.g1 (n := k) g) = Circuit.g1 g := rfl

theorem Circuit.pad_g2 (n : ℕ) {k : ℕ} (g : Gate 2) :
    Circuit.pad n (Circuit.g2 (n := k) g) = Circuit.g2 g := rfl

theorem Circuit.pad_g3 (n : ℕ) {k : ℕ} (g : Gate 3) :
    Circuit.pad n (Circuit.g3 (n := k) g) = Circuit.g3 g := rfl

end QCert
