/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits modulo the rules and the scalars

`Gs p g n` is the group of `n`-wire circuits modulo the rules and the
powers of the scalar `-ω` (central by the structural rules): the
projective setting in which the Pauli calculus of Proposition 4.8 is
derived (`PauliOne.lean`, `PauliTwo.lean`).  Moving up one wire (`ιs`) and
idle wires on top (`pads`) descend to it, and circuits on disjoint wires
commute (`commute_pads_ιs`, `commute_pads2_ιs2`).  The same commutations
hold exactly, in `CG` (`commute_padG_ι`, `commute_padG2_ι2`), and moving up
or padding keeps the Pauli group (`ι_pauliSub`, `padG_pauliSub`).
-/
import QCert.QuditClifford.SymplecticComplete

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-! ### The scalars -/

variable (p g) in
/-- The class of the scalar `-ω`. -/
noncomputable abbrev νc (n : ℕ) : CG p g n := mk p g n negω

omit [OddGen p g] in
theorem νc_comm {n : ℕ} (x : CG p g n) : Commute (νc p g n) x := by
  obtain ⟨w, rfl⟩ := mk_surjective n x
  have := scalar_pow_comm p g (n := n) 1 w
  simp only [pow_one] at this
  show mk p g n negω * mk p g n w = mk p g n w * mk p g n negω
  rw [← map_mul, ← map_mul]
  exact mk_eq_mk.2 this

theorem νc_pow_two_p {n : ℕ} : νc p g n ^ (2 * p) = 1 := by
  have h := derives_rule p g (n := n) Rule.C0
  rw [map_pow, map_one] at h
  rw [νc, ← map_pow, ← map_one (mk p g n)]
  exact mk_eq_mk.2 h

variable (p g) in
/-- The powers of the scalar. -/
noncomputable def Sc (n : ℕ) : Subgroup (CG p g n) := Subgroup.zpowers (νc p g n)

instance (n : ℕ) : (Sc p g n).Normal where
  conj_mem := by
    intro x hx y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [((νc_comm y).zpow_left k).symm.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k

variable (p g) in
/-- Circuits modulo the rules and the scalars. -/
abbrev Gs (n : ℕ) := CG p g n ⧸ Sc p g n

variable (p g) in
/-- The class of a circuit modulo the rules and the scalars. -/
noncomputable def qs (n : ℕ) : Circ n →* Gs p g n := (QuotientGroup.mk' (Sc p g n)).comp (mk p g n)

theorem qs_surjective (n : ℕ) : Function.Surjective (qs p g n) :=
  (QuotientGroup.mk'_surjective _).comp (mk_surjective n)

theorem qs_eq_of_derives {n : ℕ} {w v : Circ n} (h : Derives (Padded (Rule p g)) n w v) :
    qs p g n w = qs p g n v := by
  simp only [qs, MonoidHom.comp_apply, mk_eq_mk.2 h]

theorem qs_rule (n : ℕ) {k : ℕ} {w v : Circ k} (h : Rule p g k w v) :
    qs p g (n + k) (Circuit.pad n w) = qs p g (n + k) (Circuit.pad n v) :=
  qs_eq_of_derives (derives_rule p g h)

theorem qs_negω {n : ℕ} : qs p g n negω = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)

theorem qs_gate0 {n : ℕ} (c : Gate 0) : qs p g n (FreeMonoid.of (Gen.gate0 c)) = 1 := by
  cases c; exact qs_negω

theorem qs_neg1 {n : ℕ} : qs p g n (neg1 p) = 1 := by rw [neg1, map_pow, qs_negω, one_pow]

theorem qs_ω {n : ℕ} : qs p g n (ω p) = 1 := by rw [ω, map_pow, qs_negω, one_pow]

/-- Induction over classes, one generator at a time. -/
theorem Gs.induction_on {n : ℕ} {P : Gs p g n → Prop} (x : Gs p g n) (h1 : P 1)
    (hmul : ∀ (y : Gen Gate n) (x : Gs p g n), P x → P (qs p g n (FreeMonoid.of y) * x)) : P x := by
  obtain ⟨w, rfl⟩ := qs_surjective n x
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact h1
  | mul_of y w ih => rw [map_mul]; exact hmul y _ ih

theorem Sc_le_pauliSub (n : ℕ) : Sc p g n ≤ PauliSub p g n :=
  (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inl rfl))

/-- An element equal modulo the scalars to a Pauli is a Pauli. -/
theorem mem_pauliSub_of_eq {n : ℕ} {x t : CG p g n} (ht : t ∈ PauliSub p g n)
    (h : QuotientGroup.mk' (Sc p g n) x = QuotientGroup.mk' (Sc p g n) t) : x ∈ PauliSub p g n := by
  have h' : x⁻¹ * t ∈ Sc p g n := (QuotientGroup.eq).1 h
  have e : x = t * (x⁻¹ * t)⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ ht (Subgroup.inv_mem _ (Sc_le_pauliSub n h'))

/-! ### Moving up one wire and padding -/

theorem Sc_le_comap_ι (n : ℕ) : Sc p g n ≤ (Sc p g (n + 1)).comap (ι p g n) := by
  refine (Subgroup.zpowers_le).2 ?_
  rw [Subgroup.mem_comap, νc, ι_mk, mk_shift_negω]
  exact Subgroup.mem_zpowers _

variable (p g) in
/-- Moving a class up one wire. -/
noncomputable def ιs (n : ℕ) : Gs p g n →* Gs p g (n + 1) :=
  QuotientGroup.map _ _ (ι p g n) (Sc_le_comap_ι n)

@[simp] theorem ιs_qs {n : ℕ} (w : Circ n) : ιs p g n (qs p g n w) = qs p g (n + 1) (Circuit.shift w) :=
  rfl

omit [OddGen p g] in
theorem mk_pad_negω (n k : ℕ) : mk p g (n + k) (Circuit.pad n negω) = mk p g (n + k) negω := rfl

theorem Sc_le_comap_pad (n k : ℕ) : Sc p g k ≤ (Sc p g (n + k)).comap (padG p g n k) := by
  refine (Subgroup.zpowers_le).2 ?_
  rw [Subgroup.mem_comap, νc, padG_mk, mk_pad_negω]
  exact Subgroup.mem_zpowers _

variable (p g) in
/-- A class on `k` wires on the bottom `k` of `n + k` wires. -/
noncomputable def pads (n k : ℕ) : Gs p g k →* Gs p g (n + k) :=
  QuotientGroup.map _ _ (padG p g n k) (Sc_le_comap_pad n k)

@[simp] theorem pads_qs (n : ℕ) {k : ℕ} (w : Circ k) :
    pads p g n k (qs p g k w) = qs p g (n + k) (Circuit.pad n w) := rfl

theorem qs_up {n : ℕ} (y : Gen Gate n) :
    qs p g (n + 1) (FreeMonoid.of y.up) = ιs p g n (qs p g n (FreeMonoid.of y)) := rfl

/-! ### Disjoint wires commute modulo the scalars -/

theorem commute_of_gens_s {n k m : ℕ} (f : Gs p g k →* Gs p g n) (f' : Gs p g m →* Gs p g n)
    (h : ∀ (y : Gen Gate k) (z : Gen Gate m),
      Commute (f (qs p g k (FreeMonoid.of y))) (f' (qs p g m (FreeMonoid.of z))))
    (a : Gs p g k) (b : Gs p g m) : Commute (f a) (f' b) := by
  refine Gs.induction_on (P := fun a => Commute (f a) (f' b)) a (by simp) ?_
  intro y a ha
  rw [map_mul]
  refine Commute.mul_left ?_ ha
  refine Gs.induction_on (P := fun b => Commute (f (qs p g k (FreeMonoid.of y))) (f' b)) b
    (by simp) ?_
  intro z b hb
  rw [map_mul]
  exact Commute.mul_right (h y z) hb

theorem commute_qs_of_lift {n : ℕ} {a b : Gen Gate n}
    (h : Theory p g n (FreeMonoid.of a * FreeMonoid.of b) (FreeMonoid.of b * FreeMonoid.of a)) :
    Commute (qs p g n (FreeMonoid.of b)) (qs p g n (FreeMonoid.of a)) := by
  have := qs_eq_of_derives (Derivable.of h)
  rw [map_mul, map_mul] at this
  exact this.symm

/-- A one-wire class on wire 0 commutes with a class moved up one wire. -/
theorem commute_pads_ιs {n : ℕ} (a : Gs p g 1) (b : Gs p g n) : Commute (pads p g n 1 a) (ιs p g n b) := by
  refine commute_of_gens_s (pads p g n 1) (ιs p g n) ?_ a b
  intro y z
  rw [pads_qs, ιs_qs]
  rcases y with c | c | _ | _ | y
  · exact (show qs p g (n + 1) (FreeMonoid.of (Gen.gate0 c)) = 1 from qs_gate0 c) ▸ Commute.one_left _
  · exact commute_qs_of_lift (Lift.comm1 c z)
  · rcases y with c | _ | _ | _ | _
    show Commute (qs p g (n + 1) (Circuit.shift (FreeMonoid.of (Gen.gate0 c)))) _
    rw [← ιs_qs, qs_gate0, map_one]; exact Commute.one_left _

/-! ### Disjoint wires commute exactly -/

theorem commute_of_gens_CG {n k m : ℕ} (f : CG p g k →* CG p g n) (f' : CG p g m →* CG p g n)
    (h : ∀ (y : Gen Gate k) (z : Gen Gate m),
      Commute (f (mk p g k (FreeMonoid.of y))) (f' (mk p g m (FreeMonoid.of z))))
    (a : CG p g k) (b : CG p g m) : Commute (f a) (f' b) := by
  refine CG.induction_on (P := fun a => Commute (f a) (f' b)) a (by simp) ?_
  intro y a ha
  rw [map_mul]
  refine Commute.mul_left ?_ ha
  refine CG.induction_on (P := fun b => Commute (f (mk p g k (FreeMonoid.of y))) (f' b)) b
    (by simp) ?_
  intro z b hb
  rw [map_mul]
  exact Commute.mul_right (h y z) hb

omit [OddGen p g] in
theorem commute_mk_of_lift {n : ℕ} {a b : Gen Gate n}
    (h : Theory p g n (FreeMonoid.of a * FreeMonoid.of b) (FreeMonoid.of b * FreeMonoid.of a)) :
    Commute (mk p g n (FreeMonoid.of b)) (mk p g n (FreeMonoid.of a)) := by
  have := mk_eq_mk.2 (Derivable.of h)
  rw [map_mul, map_mul] at this
  exact this.symm

theorem mk_gate0_comm {n : ℕ} (c : Gate 0) (x : CG p g n) :
    Commute (mk p g n (FreeMonoid.of (Gen.gate0 c))) x := by
  cases c; exact νc_comm x

/-- A one-wire class on wire 0 commutes with a class moved up one wire, exactly. -/
theorem commute_padG_ι {n : ℕ} (a : CG p g 1) (b : CG p g n) :
    Commute (padG p g n 1 a) (ι p g n b) := by
  refine commute_of_gens_CG (padG p g n 1) (ι p g n) ?_ a b
  intro y z
  rw [padG_mk, ι_mk]
  rcases y with c | c | _ | _ | y
  · show Commute (mk p g (n + 1) (FreeMonoid.of (Gen.gate0 c))) _
    exact mk_gate0_comm c _
  · exact commute_mk_of_lift (Lift.comm1 c z)
  · rcases y with c | _ | _ | _ | _
    show Commute (mk p g (n + 1) (Circuit.shift (FreeMonoid.of (Gen.gate0 c)))) _
    rw [← ι_mk, ← ι_mk]
    exact (mk_gate0_comm c _).map (ι p g n)

/-- A two-wire class on wires 0, 1 commutes with a class moved up two wires, exactly. -/
theorem commute_padG2_ι2 {n : ℕ} (a : CG p g 2) (b : CG p g n) :
    Commute (padG p g n 2 a) (ι p g (n + 1) (ι p g n b)) := by
  refine commute_of_gens_CG (padG p g n 2) ((ι p g (n + 1)).comp (ι p g n)) ?_ a b
  intro y z
  rw [padG_mk, MonoidHom.comp_apply, ι_mk, ι_mk]
  rcases y with c | c | c | _ | y
  · show Commute (mk p g (n + 2) (FreeMonoid.of (Gen.gate0 c))) _
    exact mk_gate0_comm c _
  · exact commute_mk_of_lift (Lift.comm1 c z.up)
  · cases c; exact commute_mk_of_lift (Lift.comm2 Gate.CZ z)
  · rcases y with c | c | _ | _ | y
    · show Commute (mk p g (n + 2) (Circuit.shift (FreeMonoid.of (Gen.gate0 c)))) _
      rw [← ι_mk, ← ι_mk, ← ι_mk]
      exact (mk_gate0_comm c _).map (ι p g (n + 1))
    · show Commute (mk p g (n + 2) (Circuit.shift (FreeMonoid.of (Gen.gate1 c)))) _
      rw [← ι_mk, ← ι_mk]
      exact (commute_mk_of_lift (Lift.comm1 c z)).map (ι p g (n + 1))
    · rcases y with c | _ | _ | _ | _
      show Commute (mk p g (n + 2) (Circuit.shift (Circuit.shift (FreeMonoid.of (Gen.gate0 c))))) _
      rw [← ι_mk, ← ι_mk, ← ι_mk, ← ι_mk]
      exact ((mk_gate0_comm c _).map (ι p g n)).map (ι p g (n + 1))

/-! ### Moving up and padding keep the Pauli group -/

theorem ι_pauliSub {n : ℕ} {x : CG p g n} (hx : x ∈ PauliSub p g n) :
    ι p g n x ∈ PauliSub p g (n + 1) := by
  have : PauliSub p g n ≤ (PauliSub p g (n + 1)).comap (ι p g n) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | ⟨i, rfl | rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_comap, ι_mk]
    · rw [mk_shift_negω]; exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr ⟨i.succ, Or.inl rfl⟩)
    · exact Subgroup.subset_closure (Or.inr ⟨i.succ, Or.inr rfl⟩)
  exact this hx

theorem padG_pauliSub (n : ℕ) {k : ℕ} {x : CG p g k} (hx : x ∈ PauliSub p g k) :
    padG p g n k x ∈ PauliSub p g (n + k) := by
  have : PauliSub p g k ≤ (PauliSub p g (n + k)).comap (padG p g n k) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x (rfl | ⟨i, rfl | rfl⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_comap, padG_mk]
    · exact Subgroup.subset_closure (Or.inl rfl)
    · rw [pad_onWire]; exact Subgroup.subset_closure (Or.inr ⟨_, Or.inl rfl⟩)
    · rw [pad_onWire]; exact Subgroup.subset_closure (Or.inr ⟨_, Or.inr rfl⟩)
  exact this hx

end QCert.QuditClifford
