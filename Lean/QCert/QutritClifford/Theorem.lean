/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Qutrit Clifford circuits: the main results

Li, Mosca, Ross, van de Wetering and Zhao, *A Complete and Natural Rule Set
for Multi-Qutrit Clifford Circuits* (QPL 2025, arXiv:2508.14670).

* `sound`: the rules of Figure 1 only equate circuits with the same
  operator;
* `complete` (Theorem 4.4): circuits with the same operator are equal by
  the rules of Figure 1;
* `subpresentation`: the two together, with every generator invertible
  modulo the rules — the rules present the group of operators that
  `n`-qutrit circuits denote, at every `n`;
* `presentation`: the rules present the `n`-qutrit Clifford group `𝒞ₙ`
  (Definition 2.3 over `ℤ[1/3, ω]`), which `-ω`, `H`, `S` and `CZ` generate
  (Proposition 3.9 and Corollary B.3);
* `card_cliffordGroup` (Corollary 3.10): `|𝒞ₙ| = 6 ∏ₖ₌₁ⁿ 3 (9ᵏ - 1) 9ᵏ`.

The remaining `sorry`s are listed in `README.md`.
-/
import QCert.QutritClifford.Phases

namespace QCert.QutritClifford

open Matrix

/-! ### Completeness -/

/-- **Theorem 4.4**: the eighteen rules of Figure 1 are complete for
qutrit Clifford circuits: two `n`-qutrit circuits with the same operator
are equal by the rules.

The paper's proof: every circuit rewrites to a normal form (Proposition 4.3 and Lemma 4.2,
by the 380 box relations of Appendix C, which follow from the eighteen
rules by the supplement), and normal forms with the same operator coincide
(Proposition 3.9). -/
theorem complete {n : ℕ} {w v : Circ n} (h : sem n w = sem n v) :
    Derives (Padded Rule) n w v := by
  sorry

/-- The rules of Figure 1, with the structural rules, present the group of
operators of `n`-qutrit circuits: they are sound, complete, and every
generator has an inverse modulo them. -/
theorem subpresentation (n : ℕ) : IsSubPresentationOf (Theory n) (gateSem.gen (n := n)) where
  grouplike := grouplike n
  sound _ _ h := theory_sound h
  complete _ _ h := complete h

/-! ### The Clifford group -/

/-- Every generator's operator lies in the Clifford group. -/
theorem gen_mem_cliffordGroup {n : ℕ} (g : Gen Gate n) : gateSem.gen g ∈ cliffordGroup n :=
  gen_mem g

/-- The operator of a generator, as an element of the Clifford group. -/
noncomputable def cliffordGen (n : ℕ) (g : Gen Gate n) : cliffordGroup n :=
  ⟨gateSem.gen g, gen_mem_cliffordGroup g⟩

/-- **Proposition 3.9**, existence: every element of `𝒞ₙ` acts on `𝒫ₙ` as
some circuit does (the paper builds a normal form, Lemmas 3.5–3.8). -/
theorem exists_circuit_action {n : ℕ} (U : cliffordGroup n) :
    ∃ w : Circ n, ∀ P ∈ pauliGroup n,
      ((sem n w : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) * P *
        star ((sem n w : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) =
      ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) * P *
        star ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) := by
  sorry

/-- **Generation** (Proposition 3.9 with Corollary B.3): every element of
`𝒞ₙ` is the operator of a circuit over `-ω`, `H`, `S` and `CZ`: a circuit
acting on `𝒫ₙ` as it does (`exists_circuit_action`) differs from it by a
power of `-ω` (`same_action_phase`), which is a circuit too. -/
theorem cliffordGroup_le_closure (n : ℕ) :
    cliffordGroup n ≤ Subgroup.closure (Set.range (gateSem.gen (n := n))) := by
  intro U hU
  have hle : Subgroup.closure (Set.range (gateSem.gen (n := n))) ≤ cliffordGroup n :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 gen_mem_cliffordGroup)
  obtain ⟨w, hw⟩ := exists_circuit_action ⟨U, hU⟩
  have hsem : sem n w ∈ Subgroup.closure (Set.range (gateSem.gen (n := n))) := by
    have hrange : (Subgroup.closure (Set.range (gateSem.gen (n := n)))).toSubmonoid =
        MonoidHom.mrange (gateSem.sem n) :=
      ((subpresentation n).mrange_eq_closure).symm
    show sem n w ∈ (Subgroup.closure (Set.range (gateSem.gen (n := n)))).toSubmonoid
    rw [hrange]
    exact ⟨w, rfl⟩
  obtain ⟨t, -, ht⟩ := same_action_phase ⟨U, hU⟩ ⟨_, hle hsem⟩ fun P hP => (hw P hP).symm
  have hg : gateSem.gen (Gen.gate0 Gate.negω : Gen Gate n) ∈
      Subgroup.closure (Set.range (gateSem.gen (n := n))) :=
    Subgroup.subset_closure ⟨_, rfl⟩
  have hU' : U = gateSem.gen (Gen.gate0 Gate.negω : Gen Gate n) ^ t * sem n w := by
    apply Subtype.ext
    rw [Submonoid.coe_mul, SubmonoidClass.coe_pow]
    show _ = ((-ωℂ) • (1 : Op ℂ 3 n)) ^ t * _
    rw [smul_pow, one_pow, smul_mul_assoc, one_mul]
    exact ht
  rw [hU']
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hg t) hsem

theorem lift_cliffordGen {n : ℕ} (w : Circ n) :
    (FreeMonoid.lift (cliffordGen n) w : unitaryGroup (State 3 n) ℂ) = sem n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, Subgroup.coe_mul, ih, FreeMonoid.lift_eval_of]
    rfl

/-- **The rules of Figure 1 present the `n`-qutrit Clifford group `𝒞ₙ`**,
for every `n`. -/
theorem presentation (n : ℕ) : IsPresentationOf (Theory n) (cliffordGen n) where
  grouplike := grouplike n
  sound w v h := Subtype.ext (by rw [lift_cliffordGen, lift_cliffordGen]; exact theory_sound h)
  complete w v h := complete (by
    have := congrArg Subtype.val h
    rwa [lift_cliffordGen, lift_cliffordGen] at this)
  surjective := by
    rintro ⟨U, hU⟩
    have hcl := cliffordGroup_le_closure n hU
    have hrange : (Subgroup.closure (Set.range (gateSem.gen (n := n)))).toSubmonoid =
        MonoidHom.mrange (gateSem.sem n) :=
      ((subpresentation n).mrange_eq_closure).symm
    have : U ∈ MonoidHom.mrange (gateSem.sem n) := by
      rw [← hrange]; exact hcl
    obtain ⟨w, hw⟩ := this
    exact ⟨w, Subtype.ext (by rw [lift_cliffordGen]; exact hw)⟩

/-- **Corollary 3.10**: `|𝒞ₙ| = 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ - 1) 9ᵏ`. -/
theorem card_cliffordGroup (n : ℕ) :
    Nat.card (cliffordGroup n) = 6 * ∏ k ∈ Finset.Icc 1 n, 3 * (9 ^ k - 1) * 9 ^ k := by
  sorry

end QCert.QutritClifford
