/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CNOT-dihedral circuits: basic derivations

`Eqv n w v`: `w` and `v` are equal in the theory of CNOT-dihedral circuits
on `n` wires.  Derivations move up a wire (`Eqv.shift`), and a relation of
Figure 1 holds on the bottom wires of every wider circuit (`Eqv.rule`).
-/
import QCert.CNOTDihedral.Syntax

namespace QCert.CNOTDihedral

/-- A monoid homomorphism carrying the axioms of one theory into another
carries its derivations. -/
theorem derivable_map {X Y : Type*} {Γ : WRel X} {Δ : WRel Y} (φ : Word X →* Word Y)
    (h : ∀ w v, Γ w v → Derivable Δ (φ w) (φ v)) {w v : Word X} (d : Derivable Γ w v) :
    Derivable Δ (φ w) (φ v) := by
  have : conGen Γ ≤ (conGen Δ).comap φ (map_mul φ) :=
    Con.conGen_le fun x y hxy => (Con.comap_rel _).2 (h x y hxy)
  exact (Con.comap_rel _).1 (this d)

open Circuit

/-- Equality in the theory on `n` wires. -/
abbrev Eqv (n : ℕ) (w v : Circ n) : Prop := Derivable (Theory n) w v

namespace Eqv

variable {n : ℕ} {w v u w' v' : Circ n}

@[refl] theorem refl (w : Circ n) : Eqv n w w := Derivable.refl w
@[symm] theorem symm (h : Eqv n w v) : Eqv n v w := Derivable.symm h
@[trans] theorem trans (h : Eqv n w v) (h' : Eqv n v u) : Eqv n w u := Derivable.trans h h'
theorem mul (h : Eqv n w v) (h' : Eqv n w' v') : Eqv n (w * w') (v * v') := Derivable.mul h h'
theorem of_eq (h : w = v) : Eqv n w v := h ▸ refl w

theorem mul_left (u : Circ n) (h : Eqv n w v) : Eqv n (u * w) (u * v) := mul (refl u) h
theorem mul_right (u : Circ n) (h : Eqv n w v) : Eqv n (w * u) (v * u) := mul h (refl u)

/-- A derivation moved up one wire. -/
theorem shift (h : Eqv n w v) : Eqv (n + 1) (Circuit.shift w) (Circuit.shift v) :=
  derivable_map Circuit.shift (fun _ _ r => Derivable.of (Lift.shift r)) h

/-- A relation of Figure 1 on the bottom wires of a wider circuit. -/
theorem rule {k : ℕ} (m : ℕ) {w v : Circ k} (r : Rel k w v) :
    Eqv (m + k) (Circuit.pad m w) (Circuit.pad m v) :=
  Derivable.of (Lift.rule (Padded.pad m r))

end Eqv

end QCert.CNOTDihedral
