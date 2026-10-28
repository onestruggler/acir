/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits modulo the rules and the Paulis

`Gh p g n` is the group of `n`-wire circuits modulo the rules and modulo
the normal closure of the Pauli group: the setting of the paper's
"symplectic completeness" (Theorem 4.4), where `X`, `Z` and the scalars
are trivial.  The action on Paulis factors through it (`σh`), and so do
moving up one wire (`ιh`) and idle wires on top (`padh`).

Circuits on disjoint wires commute: a one-wire circuit on wire 0 with a
circuit moved up one wire (`commute_padh_ιh`), a two-wire circuit on
wires 0, 1 with a circuit moved up two wires (`commute_padh2_ιh2`).
-/
import QCert.QuditClifford.SymplecticCalc

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime] (g : ZMod p) [OddGen p g]

/-- Circuits modulo the rules and the Pauli group. -/
abbrev Gh (n : ℕ) := CG p g n ⧸ PauliN p g n

/-- The class of a circuit modulo the rules and the Paulis. -/
noncomputable def qh (n : ℕ) : Circ n →* Gh p g n := (QuotientGroup.mk' (PauliN p g n)).comp (mk p g n)

variable {p g}

theorem qh_surjective (n : ℕ) : Function.Surjective (qh p g n) :=
  (QuotientGroup.mk'_surjective _).comp (mk_surjective n)

theorem qh_eq_of_derives {n : ℕ} {w v : Circ n} (h : Derives (Padded (Rule p g)) n w v) :
    qh p g n w = qh p g n v := by
  simp only [qh, MonoidHom.comp_apply, mk_eq_mk.2 h]

theorem qh_rule (n : ℕ) {k : ℕ} {w v : Circ k} (h : Rule p g k w v) :
    qh p g (n + k) (Circuit.pad n w) = qh p g (n + k) (Circuit.pad n v) :=
  qh_eq_of_derives (derives_rule p g h)

theorem qh_eq_one_of_mem {n : ℕ} {w : Circ n} (h : mk p g n w ∈ PauliN p g n) : qh p g n w = 1 :=
  (QuotientGroup.eq_one_iff _).2 h

theorem qh_negω {n : ℕ} : qh p g n negω = 1 :=
  qh_eq_one_of_mem (Subgroup.subset_normalClosure (Or.inl rfl))

theorem qh_gate0 {n : ℕ} (c : Gate 0) : qh p g n (FreeMonoid.of (Gen.gate0 c)) = 1 := by
  cases c; exact qh_negω

/-- Induction over classes, one generator at a time. -/
theorem Gh.induction_on {n : ℕ} {P : Gh p g n → Prop} (x : Gh p g n) (h1 : P 1)
    (hmul : ∀ (y : Gen Gate n) (x : Gh p g n), P x → P (qh p g n (FreeMonoid.of y) * x)) : P x := by
  obtain ⟨w, rfl⟩ := qh_surjective n x
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact h1
  | mul_of y w ih => rw [map_mul]; exact hmul y _ ih

/-! ### The action on Paulis -/

theorem pauliN_le_ker_σG (n : ℕ) : PauliN p g n ≤ (σG (g := g) n).ker := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (rfl | ⟨i, rfl | rfl⟩)
  · exact (MonoidHom.mem_ker).2 (σC_negω p)
  · exact (MonoidHom.mem_ker).2 (σC_onWire p i (σC_X p))
  · exact (MonoidHom.mem_ker).2 (σC_onWire p i (σC_Z p))

/-- The action of a class on Paulis modulo phases. -/
noncomputable def σh (n : ℕ) : Gh p g n →* Function.End (V p n) :=
  QuotientGroup.lift _ (σG n) (pauliN_le_ker_σG n)

@[simp] theorem σh_qh {n : ℕ} (w : Circ n) : σh n (qh p g n w) = σC p n w := rfl

/-! ### Moving up one wire -/

omit [OddGen p g] in
theorem mk_shift_negω {n : ℕ} : mk p g (n + 1) (Circuit.shift negω) = mk p g (n + 1) negω :=
  mk_eq_mk.2 (Derivable.of (Lift.scalar Gate.negω))

theorem pauliN_le_comap_ι (n : ℕ) : PauliN p g n ≤ (PauliN p g (n + 1)).comap (ι p g n) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (rfl | ⟨i, rfl | rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_comap, ι_mk]
  · rw [mk_shift_negω]; exact Subgroup.subset_normalClosure (Or.inl rfl)
  · exact Subgroup.subset_normalClosure (Or.inr ⟨i.succ, Or.inl rfl⟩)
  · exact Subgroup.subset_normalClosure (Or.inr ⟨i.succ, Or.inr rfl⟩)

/-- Moving a class up one wire. -/
noncomputable def ιh (n : ℕ) : Gh p g n →* Gh p g (n + 1) :=
  QuotientGroup.map _ _ (ι p g n) (pauliN_le_comap_ι n)

@[simp] theorem ιh_qh {n : ℕ} (w : Circ n) : ιh n (qh p g n w) = qh p g (n + 1) (Circuit.shift w) := rfl

theorem σh_ιh {n : ℕ} (x : Gh p g n) (v : V p (n + 1)) :
    σh (n + 1) (ιh n x) v = Fin.cons (v 0) (σh n x (Fin.tail v)) := by
  obtain ⟨w, rfl⟩ := qh_surjective n x
  exact σC_shift p w v

/-! ### Idle wires on top -/

theorem pad_onWire (n : ℕ) : {k : ℕ} → (i : Fin k) → (c : Circ 1) →
    Circuit.pad n (onWire k i c) = onWire (n + k) ⟨i, by omega⟩ c
  | k + 1, ⟨0, _⟩, c => by
    show FreeMonoid.map (Gen.pad n) (FreeMonoid.map (Gen.pad k) c) = FreeMonoid.map (Gen.pad (n + k)) c
    rw [FreeMonoid.map_map]
    congr 2
    funext x
    rcases x with c | c | _ | _ | x
    · rfl
    · rfl
    · rcases x with c | _ | _ | _ | _
      rfl
  | k + 1, ⟨i + 1, h⟩, c => by
    show Circuit.pad n (Circuit.shift (onWire k ⟨i, by omega⟩ c)) = _
    rw [pad_shift, pad_onWire n ⟨i, by omega⟩ c]
    rfl

theorem pauliN_le_comap_pad (n k : ℕ) : PauliN p g k ≤ (PauliN p g (n + k)).comap (padG p g n k) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (rfl | ⟨i, rfl | rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_comap, padG_mk]
  · exact Subgroup.subset_normalClosure (Or.inl rfl)
  · rw [pad_onWire]; exact Subgroup.subset_normalClosure (Or.inr ⟨_, Or.inl rfl⟩)
  · rw [pad_onWire]; exact Subgroup.subset_normalClosure (Or.inr ⟨_, Or.inr rfl⟩)

/-- A class on `k` wires on the bottom `k` of `n + k` wires. -/
noncomputable def padh (n k : ℕ) : Gh p g k →* Gh p g (n + k) :=
  QuotientGroup.map _ _ (padG p g n k) (pauliN_le_comap_pad n k)

@[simp] theorem padh_qh (n : ℕ) {k : ℕ} (w : Circ k) :
    padh n k (qh p g k w) = qh p g (n + k) (Circuit.pad n w) := rfl

theorem σh_padh (n : ℕ) {k : ℕ} (x : Gh p g k) (v : V p (n + k)) :
    σh (n + k) (padh n k x) v = withLow p (σh k x (low p v)) v := by
  obtain ⟨w, rfl⟩ := qh_surjective k x
  exact σC_pad p n w v

/-! ### Disjoint wires commute -/

theorem qh_up {n : ℕ} (y : Gen Gate n) :
    qh p g (n + 1) (FreeMonoid.of y.up) = ιh n (qh p g n (FreeMonoid.of y)) := rfl

/-- Commutation of all classes from the commutation of generators. -/
theorem commute_of_gens {n k m : ℕ} (f : Gh p g k →* Gh p g n) (f' : Gh p g m →* Gh p g n)
    (h : ∀ (y : Gen Gate k) (z : Gen Gate m),
      Commute (f (qh p g k (FreeMonoid.of y))) (f' (qh p g m (FreeMonoid.of z))))
    (a : Gh p g k) (b : Gh p g m) : Commute (f a) (f' b) := by
  refine Gh.induction_on (P := fun a => Commute (f a) (f' b)) a (by simp) ?_
  intro y a ha
  rw [map_mul]
  refine Commute.mul_left ?_ ha
  refine Gh.induction_on (P := fun b => Commute (f (qh p g k (FreeMonoid.of y))) (f' b)) b (by simp) ?_
  intro z b hb
  rw [map_mul]
  exact Commute.mul_right (h y z) hb

theorem commute_qh_of_lift {n : ℕ} {a b : Gen Gate n}
    (h : Theory p g n (FreeMonoid.of a * FreeMonoid.of b) (FreeMonoid.of b * FreeMonoid.of a)) :
    Commute (qh p g n (FreeMonoid.of b)) (qh p g n (FreeMonoid.of a)) := by
  have := qh_eq_of_derives (Derivable.of h)
  rw [map_mul, map_mul] at this
  exact this.symm

/-- A one-wire class on wire 0 commutes with a class moved up one wire. -/
theorem commute_padh_ιh {n : ℕ} (a : Gh p g 1) (b : Gh p g n) : Commute (padh n 1 a) (ιh n b) := by
  refine commute_of_gens (padh n 1) (ιh n) ?_ a b
  intro y z
  rw [padh_qh, ιh_qh]
  rcases y with c | c | _ | _ | y
  · exact (show qh p g (n + 1) (FreeMonoid.of (Gen.gate0 c)) = 1 from qh_gate0 c) ▸ Commute.one_left _
  · exact commute_qh_of_lift (Lift.comm1 c z)
  · rcases y with c | _ | _ | _ | _
    show Commute (qh p g (n + 1) (Circuit.shift (FreeMonoid.of (Gen.gate0 c)))) _
    rw [← ιh_qh, qh_gate0, map_one]; exact Commute.one_left _

/-- A two-wire class on wires 0, 1 commutes with a class moved up two wires. -/
theorem commute_padh2_ιh2 {n : ℕ} (a : Gh p g 2) (b : Gh p g n) :
    Commute (padh n 2 a) (ιh (n + 1) (ιh n b)) := by
  refine commute_of_gens (padh n 2) ((ιh (n + 1)).comp (ιh n)) ?_ a b
  intro y z
  rw [padh_qh, MonoidHom.comp_apply, ιh_qh, ιh_qh]
  rcases y with c | c | c | _ | y
  · exact (show qh p g (n + 2) (FreeMonoid.of (Gen.gate0 c)) = 1 from qh_gate0 c) ▸ Commute.one_left _
  · exact commute_qh_of_lift (Lift.comm1 c z.up)
  · cases c; exact commute_qh_of_lift (Lift.comm2 Gate.CZ z)
  · rcases y with c | c | _ | _ | y
    · show Commute (qh p g (n + 2) (Circuit.shift (FreeMonoid.of (Gen.gate0 c)))) _
      rw [← ιh_qh, qh_gate0, map_one]; exact Commute.one_left _
    · show Commute (qh p g (n + 2) (Circuit.shift (FreeMonoid.of (Gen.gate1 c)))) _
      rw [← ιh_qh, ← ιh_qh]
      exact (commute_qh_of_lift (Lift.comm1 c z)).map (ιh (n + 1))
    · rcases y with c | _ | _ | _ | _
      show Commute (qh p g (n + 2) (Circuit.shift (Circuit.shift (FreeMonoid.of (Gen.gate0 c))))) _
      rw [← ιh_qh, ← ιh_qh, qh_gate0, map_one, map_one]; exact Commute.one_left _

end QCert.QuditClifford
