/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The Pauli group is normal

The derivations of Proposition 4.8 (`PauliOne.lean`, `PauliTwo.lean`),
which hold up to scalars, place the conjugate of every Pauli generator by
every gate in the Pauli group (scalars being Paulis): on its own wires by
the one- and two-wire calculus, on other wires because disjoint wires
commute, and for gates moved up a wire by induction on the width
(`conj_gen`).  So the Pauli group is normal (`pauliSub_normal`), and its
normal closure is itself: `pauli_normal`, which with Theorem 4.4 is the
step of Proposition 4.9 used in the proof of Theorem 4.10.
-/
import QCert.QuditClifford.PauliTwo

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### Paulis on a wire -/

/-- The one-wire Paulis `X`, `Z`. -/
def IsXZ (p : ℕ) (w : Circ 1) : Prop := w = X p ∨ w = Z p

theorem onWire_mem {n : ℕ} (i : Fin n) {w : Circ 1} (hw : IsXZ p w) :
    mk p g n (onWire n i w) ∈ PauliSub p g n := by
  rcases hw with rfl | rfl
  · exact Subgroup.subset_closure (Or.inr ⟨i, Or.inl rfl⟩)
  · exact Subgroup.subset_closure (Or.inr ⟨i, Or.inr rfl⟩)

theorem negω_mem_sub {n : ℕ} : mk p g n negω ∈ PauliSub p g n := Subgroup.subset_closure (Or.inl rfl)

theorem onWire1_0 (c : Circ 1) : onWire 1 ⟨0, Nat.one_pos⟩ c = c := pad_zero_one c

theorem onWire2_1 (w : Circ 1) :
    onWire 2 ⟨1, by omega⟩ w = top w := by
  show Circuit.shift (Circuit.pad 0 w) = Circuit.shift w
  rw [pad_zero_one]

theorem mem1 {w : Circ 1} (hw : IsXZ p w) : mk p g 1 w ∈ PauliSub p g 1 := by
  have := onWire_mem (g := g) ⟨0, Nat.one_pos⟩ hw
  rwa [onWire1_0] at this

theorem mem_bot {w : Circ 1} (hw : IsXZ p w) : mk p g 2 (bot w) ∈ PauliSub p g 2 :=
  onWire_mem (g := g) (n := 2) ⟨0, by omega⟩ hw

theorem mem_top {w : Circ 1} (hw : IsXZ p w) : mk p g 2 (top w) ∈ PauliSub p g 2 := by
  have := onWire_mem (g := g) (n := 2) ⟨1, by omega⟩ hw
  rwa [onWire2_1] at this

theorem conj_negω_mem_sub {n : ℕ} (y : CG p g n) : y * mk p g n negω * y⁻¹ ∈ PauliSub p g n := by
  rw [conj_of_commute (νc_comm y).symm]; exact negω_mem_sub

/-! ### One and two wires -/

theorem conj1 (c : Gate 1) {w : Circ 1} (hw : IsXZ p w) :
    mk p g 1 (Circuit.g1 c) * mk p g 1 w * (mk p g 1 (Circuit.g1 c))⁻¹ ∈ PauliSub p g 1 := by
  have hX : IsXZ p (X p) := Or.inl rfl
  have hZ : IsXZ p (Z p) := Or.inr rfl
  cases c <;> rcases hw with rfl | rfl
  · refine mem_pauliSub_of_eq (mem1 hZ) ?_
    simp only [map_mul, map_inv]
    exact qs_HXH
  · refine mem_pauliSub_of_eq (Subgroup.inv_mem _ (mem1 hX)) ?_
    simp only [map_mul, map_inv]
    exact qs_HZH
  · refine mem_pauliSub_of_eq (Subgroup.mul_mem _ (mem1 hX) (mem1 hZ)) ?_
    simp only [map_mul, map_inv]
    exact qs_SXS
  · refine mem_pauliSub_of_eq (mem1 hZ) ?_
    simp only [map_mul, map_inv]
    show qs p g 1 S * qs p g 1 (Z p) * (qs p g 1 S)⁻¹ = qs p g 1 (Z p)
    rw [qs_SZ]; gnorm

theorem conj2 (i : Fin 2) {w : Circ 1} (hw : IsXZ p w) :
    mk p g 2 CZ * mk p g 2 (onWire 2 i w) * (mk p g 2 CZ)⁻¹ ∈ PauliSub p g 2 := by
  have hX : IsXZ p (X p) := Or.inl rfl
  have hZ : IsXZ p (Z p) := Or.inr rfl
  rcases i with ⟨_ | _ | i, hi⟩
  · show mk p g 2 CZ * mk p g 2 (bot w) * (mk p g 2 CZ)⁻¹ ∈ PauliSub p g 2
    rcases hw with rfl | rfl
    · refine mem_pauliSub_of_eq (Subgroup.mul_mem _ (mem_bot hX) (mem_top hZ)) ?_
      simp only [map_mul, map_inv]
      exact qs_C_loX
    · refine mem_pauliSub_of_eq (mem_bot hZ) ?_
      simp only [map_mul, map_inv]
      exact conj_of_commute qsC_loZ
  · show mk p g 2 CZ * mk p g 2 (Circuit.shift (Circuit.pad 0 w)) * (mk p g 2 CZ)⁻¹ ∈ PauliSub p g 2
    rw [pad_zero_one]
    rcases hw with rfl | rfl
    · refine mem_pauliSub_of_eq (Subgroup.mul_mem _ (mem_top hX) (mem_bot hZ)) ?_
      simp only [map_mul, map_inv]
      exact qs_C_hiX
    · refine mem_pauliSub_of_eq (mem_top hZ) ?_
      simp only [map_mul, map_inv]
      exact conj_of_commute qsC_hiZ
  · omega

/-! ### Every width -/

/-- Every gate conjugates `X` and `Z` on every wire into the Pauli group. -/
theorem conj_gen_wire : {n : ℕ} → (y : Gen Gate n) → (i : Fin n) → {w : Circ 1} → IsXZ p w →
    mk p g n (FreeMonoid.of y) * mk p g n (onWire n i w) * (mk p g n (FreeMonoid.of y))⁻¹ ∈
      PauliSub p g n
  | _, .gate0 c, i, w, hw => by
    rw [conj_of_commute (mk_gate0_comm c _)]; exact onWire_mem i hw
  | m + 1, .gate1 c, ⟨0, hi⟩, w, hw => by
    have e : mk p g (m + 1) (FreeMonoid.of (Gen.gate1 c)) * mk p g (m + 1) (onWire (m + 1) ⟨0, hi⟩ w) *
        (mk p g (m + 1) (FreeMonoid.of (Gen.gate1 c)))⁻¹ =
        padG p g m 1 (mk p g 1 (Circuit.g1 c) * mk p g 1 w * (mk p g 1 (Circuit.g1 c))⁻¹) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]; exact padG_pauliSub m (conj1 c hw)
  | m + 1, .gate1 c, ⟨j + 1, hj⟩, w, hw => by
    have hc := commute_padG_ι (p := p) (g := g) (mk p g 1 (Circuit.g1 c))
      (mk p g m (onWire m ⟨j, by omega⟩ w))
    have e : mk p g (m + 1) (FreeMonoid.of (Gen.gate1 c)) *
        mk p g (m + 1) (onWire (m + 1) ⟨j + 1, hj⟩ w) *
        (mk p g (m + 1) (FreeMonoid.of (Gen.gate1 c)))⁻¹ =
        mk p g (m + 1) (onWire (m + 1) ⟨j + 1, hj⟩ w) := conj_of_commute hc
    rw [e]; exact onWire_mem _ hw
  | m + 2, .gate2 c, ⟨0, hi⟩, w, hw => by
    cases c
    have e : mk p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)) *
        mk p g (m + 2) (onWire (m + 2) ⟨0, hi⟩ w) *
        (mk p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)))⁻¹ =
        padG p g m 2 (mk p g 2 CZ * mk p g 2 (onWire 2 ⟨0, by omega⟩ w) * (mk p g 2 CZ)⁻¹) := by
      rw [map_mul, map_mul, map_inv, padG_mk, padG_mk, pad_onWire]; rfl
    rw [e]; exact padG_pauliSub m (conj2 _ hw)
  | m + 2, .gate2 c, ⟨1, hi⟩, w, hw => by
    cases c
    have e : mk p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)) *
        mk p g (m + 2) (onWire (m + 2) ⟨1, hi⟩ w) *
        (mk p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)))⁻¹ =
        padG p g m 2 (mk p g 2 CZ * mk p g 2 (onWire 2 ⟨1, by omega⟩ w) * (mk p g 2 CZ)⁻¹) := by
      rw [map_mul, map_mul, map_inv, padG_mk, padG_mk, pad_onWire]; rfl
    rw [e]; exact padG_pauliSub m (conj2 _ hw)
  | m + 2, .gate2 c, ⟨j + 2, hj⟩, w, hw => by
    cases c
    have hc := commute_padG2_ι2 (p := p) (g := g) (mk p g 2 CZ)
      (mk p g m (onWire m ⟨j, by omega⟩ w))
    have e : mk p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)) *
        mk p g (m + 2) (onWire (m + 2) ⟨j + 2, hj⟩ w) *
        (mk p g (m + 2) (FreeMonoid.of (Gen.gate2 Gate.CZ)))⁻¹ =
        mk p g (m + 2) (onWire (m + 2) ⟨j + 2, hj⟩ w) := conj_of_commute hc
    rw [e]; exact onWire_mem _ hw
  | _, .gate3 c, _, _, _ => nomatch c
  | m + 1, .up y, ⟨0, hi⟩, w, hw => by
    have hc := commute_padG_ι (p := p) (g := g) (mk p g 1 w) (mk p g m (FreeMonoid.of y))
    have e : mk p g (m + 1) (FreeMonoid.of y.up) * mk p g (m + 1) (onWire (m + 1) ⟨0, hi⟩ w) *
        (mk p g (m + 1) (FreeMonoid.of y.up))⁻¹ = mk p g (m + 1) (onWire (m + 1) ⟨0, hi⟩ w) :=
      conj_of_commute hc.symm
    rw [e]; exact onWire_mem _ hw
  | m + 1, .up y, ⟨j + 1, hj⟩, w, hw => by
    have ih := conj_gen_wire y ⟨j, by omega⟩ hw
    have e : mk p g (m + 1) (FreeMonoid.of y.up) * mk p g (m + 1) (onWire (m + 1) ⟨j + 1, hj⟩ w) *
        (mk p g (m + 1) (FreeMonoid.of y.up))⁻¹ =
        ι p g m (mk p g m (FreeMonoid.of y) * mk p g m (onWire m ⟨j, by omega⟩ w) *
          (mk p g m (FreeMonoid.of y))⁻¹) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [e]; exact ι_pauliSub ih

theorem conj_gen {n : ℕ} (y : Gen Gate n) {P : CG p g n} (hP : P ∈ PauliSet p g n) :
    mk p g n (FreeMonoid.of y) * P * (mk p g n (FreeMonoid.of y))⁻¹ ∈ PauliSub p g n := by
  rcases hP with rfl | ⟨i, rfl | rfl⟩
  · exact conj_negω_mem_sub _
  · exact conj_gen_wire y i (Or.inl rfl)
  · exact conj_gen_wire y i (Or.inr rfl)

/-- Conjugating by a generator keeps the Pauli group. -/
theorem conj_gen_sub {n : ℕ} (y : Gen Gate n) {P : CG p g n} (hP : P ∈ PauliSub p g n) :
    mk p g n (FreeMonoid.of y) * P * (mk p g n (FreeMonoid.of y))⁻¹ ∈ PauliSub p g n := by
  have hP' : P ∈ Subgroup.closure (PauliSet p g n) := hP
  clear hP
  induction hP' using Subgroup.closure_induction with
  | mem t ht => exact conj_gen y ht
  | one => rw [mul_one, mul_inv_cancel]; exact Subgroup.one_mem _
  | mul t u _ _ ht hu =>
    rw [show mk p g n (FreeMonoid.of y) * (t * u) * (mk p g n (FreeMonoid.of y))⁻¹ =
      (mk p g n (FreeMonoid.of y) * t * (mk p g n (FreeMonoid.of y))⁻¹) *
        (mk p g n (FreeMonoid.of y) * u * (mk p g n (FreeMonoid.of y))⁻¹) by gnorm]
    exact Subgroup.mul_mem _ ht hu
  | inv t _ ht =>
    rw [show mk p g n (FreeMonoid.of y) * t⁻¹ * (mk p g n (FreeMonoid.of y))⁻¹ =
      (mk p g n (FreeMonoid.of y) * t * (mk p g n (FreeMonoid.of y))⁻¹)⁻¹ by gnorm]
    exact Subgroup.inv_mem _ ht

instance pauliSub_normal (n : ℕ) : (PauliSub p g n).Normal where
  conj_mem := by
    intro x hx y
    obtain ⟨w, rfl⟩ := mk_surjective n y
    induction w using FreeMonoid.inductionOn' with
    | one => rw [map_one, one_mul, inv_one, mul_one]; exact hx
    | mul_of a w ih =>
      rw [map_mul, show mk p g n (FreeMonoid.of a) * mk p g n w * x *
          (mk p g n (FreeMonoid.of a) * mk p g n w)⁻¹ =
        mk p g n (FreeMonoid.of a) * (mk p g n w * x * (mk p g n w)⁻¹) *
          (mk p g n (FreeMonoid.of a))⁻¹ by gnorm]
      exact conj_gen_sub a ih

variable (p g) in
/-- Proposition 4.9, the step used here: the normal closure of the Pauli
group is the Pauli group. -/
theorem pauli_normal (n : ℕ) : PauliN p g n ≤ PauliSub p g n :=
  Subgroup.normalClosure_le_normal (fun _ hx => Subgroup.subset_closure hx)

end QCert.QuditClifford
