/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Normal forms are the Clifford group (Proposition 3.9, Corollary 3.10)

Every element of `𝒞ₙ` is the operator of exactly one normal form
(`nfEquiv`): its action on `𝒫ₙ` is that of the layers of a normal form
(`exists_nf`), which then differ from it by a power of `-ω`
(Corollary B.3), and the normal form is determined by its operator
(`nf_unique`).  Counting the normal forms gives Corollary 3.10:
`|𝒞ₙ| = 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ - 1) 9ᵏ` (`card_cliffordGroup_eq`).
-/
import QCert.QutritClifford.Prop39

namespace QCert.QutritClifford

open Matrix

/-! ### Counting normal forms -/

/-- A `Z`-normal circuit on `n + 1` wires either leaves the bottom wire idle
or has its `A` box there. -/
def ZN.equivSucc (n : ℕ) :
    ZN (n + 1) ≃ ZN n ⊕ (AIdx × (Fin n → Fin 3 × Fin 3) × Fin 3) where
  toFun
    | .core i js c => Sum.inr (i, js, c)
    | .skip z => Sum.inl z
  invFun
    | Sum.inl z => .skip z
    | Sum.inr (i, js, c) => .core i js c
  left_inv z := by cases z <;> rfl
  right_inv x := by rcases x with z | ⟨i, js, c⟩ <;> rfl

instance ZN.fintype : (n : ℕ) → Fintype (ZN n)
  | 0 => ⟨∅, fun z => (ZN.not_zero z).elim⟩
  | n + 1 =>
    letI := ZN.fintype n
    Fintype.ofEquiv _ (ZN.equivSucc n).symm

/-- `X`-normal circuits as tuples of indices. -/
def XN.equiv (k : ℕ) : XN k ≃ (Fin k → Fin 3 × Fin 3) × Fin 3 × Fin 3 where
  toFun M := (M.ds, M.h, M.v)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (k : ℕ) : Fintype (XN k) := Fintype.ofEquiv _ (XN.equiv k).symm

instance NFX.fintype : (n : ℕ) → Fintype (NFX n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI := NFX.fintype n
    inferInstanceAs (Fintype (ZN (n + 1) × XN n × NFX n))

instance (n : ℕ) : Fintype (NF n) := inferInstanceAs (Fintype (NFX n × Fin 6))

theorem card_AIdx : Fintype.card AIdx = 8 := by decide

/-- There are `3 (9ⁿ - 1)` `Z`-normal circuits on `n` wires. -/
theorem card_ZN : ∀ n : ℕ, Fintype.card (ZN n) = 3 * (9 ^ n - 1)
  | 0 => by
    rw [pow_zero, Nat.sub_self, mul_zero, Fintype.card_eq_zero_iff]
    exact ⟨ZN.not_zero⟩
  | n + 1 => by
    rw [Fintype.card_congr (ZN.equivSucc n), Fintype.card_sum, card_ZN n, Fintype.card_prod,
      Fintype.card_prod, card_AIdx, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, pow_succ]
    have : 1 ≤ 9 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h9 : (3 * 3) ^ n = 9 ^ n := by norm_num
    rw [h9]
    omega

/-- There are `9ᵏ⁺¹` `X`-normal circuits on `k + 1` wires. -/
theorem card_XN (k : ℕ) : Fintype.card (XN k) = 9 ^ (k + 1) := by
  rw [Fintype.card_congr (XN.equiv k), Fintype.card_prod, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  norm_num [pow_succ]

theorem card_NFX : ∀ n : ℕ,
    Fintype.card (NFX n) = ∏ k ∈ Finset.Icc 1 n, 3 * (9 ^ k - 1) * 9 ^ k
  | 0 => rfl
  | n + 1 => by
    rw [show Fintype.card (NFX (n + 1)) = Fintype.card (ZN (n + 1) × XN n × NFX n) from
        Fintype.card_congr (Equiv.refl _),
      Fintype.card_prod, Fintype.card_prod, card_ZN, card_XN, card_NFX n,
      Finset.prod_Icc_succ_top (by omega)]
    ring

theorem card_NF (n : ℕ) :
    Fintype.card (NF n) = 6 * ∏ k ∈ Finset.Icc 1 n, 3 * (9 ^ k - 1) * 9 ^ k := by
  rw [show Fintype.card (NF n) = Fintype.card (NFX n × Fin 6) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_prod, card_NFX, Fintype.card_fin, mul_comm]

/-! ### Normal forms and the Clifford group -/

noncomputable section

/-- Every circuit's operator lies in `𝒞ₙ`. -/
theorem sem_mem_cliffordGroup {n : ℕ} (w : Circ n) : sem n w ∈ cliffordGroup n := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul_of g w ih =>
    rw [map_mul]
    exact Subgroup.mul_mem _ (by rw [show sem n (FreeMonoid.of g) = gateSem.gen g from
      FreeMonoid.lift_eval_of _ _]; exact gen_mem g) ih

theorem normal_of_mem {n : ℕ} (U : cliffordGroup n) :
    Normal n ((U : unitaryGroup (State 3 n) ℂ) : Op ℂ 3 n) := by
  obtain ⟨h1, h2⟩ := Unitary.mem_iff.1 (U : unitaryGroup (State 3 n) ℂ).2
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨⟨c, a, b⟩, hr⟩ := U.2.2 p.op ⟨⟨p.c, p.a, p.b⟩, rfl⟩
  exact ⟨⟨c, a, b⟩, hr.symm⟩

/-- The operator of a normal form, as an element of `𝒞ₙ`. -/
def nfOp (n : ℕ) (N : NF n) : cliffordGroup n := ⟨sem n N.circ, sem_mem_cliffordGroup _⟩

theorem nfOp_injective (n : ℕ) : Function.Injective (nfOp n) := fun _ _ h =>
  nf_unique (congrArg Subtype.val h)

/-- **Proposition 3.9**: every element of `𝒞ₙ` is the operator of a normal
form. -/
theorem nfOp_surjective (n : ℕ) : Function.Surjective (nfOp n) := by
  intro U
  obtain ⟨x, hx⟩ := exists_nf n _ (normal_of_mem U)
  obtain ⟨t, ht, hU⟩ := same_action_phase U ⟨sem n (NFX.circ n x), sem_mem_cliffordGroup _⟩
    (by
      rintro _ ⟨⟨c, a, b⟩, rfl⟩
      exact (hx ⟨c, a, b⟩).trans (sem_conj _ ⟨c, a, b⟩).symm)
  refine ⟨(x, ⟨t, ht⟩), Subtype.ext (Subtype.ext ?_)⟩
  show (sem n (NFX.circ n x * negω ^ t) : Op ℂ 3 n) = _
  rw [map_mul, Submonoid.coe_mul, sem_negω_pow, mul_smul_comm, mul_one]
  exact hU.symm

/-- Normal forms are in bijection with `𝒞ₙ`. -/
def nfEquiv (n : ℕ) : NF n ≃ cliffordGroup n :=
  Equiv.ofBijective (nfOp n) ⟨nfOp_injective n, nfOp_surjective n⟩

/-- **Corollary 3.10**. -/
theorem card_cliffordGroup_eq (n : ℕ) :
    Nat.card (cliffordGroup n) = 6 * ∏ k ∈ Finset.Icc 1 n, 3 * (9 ^ k - 1) * 9 ^ k := by
  rw [← Nat.card_congr (nfEquiv n), Nat.card_eq_fintype_card, card_NF]

end

end QCert.QutritClifford
