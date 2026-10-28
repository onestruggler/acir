/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness

Every circuit on `n + 1` wires is, in the theory, `Λ * Xc b * d` (`nf_mk`,
the paper's Proposition 5.5): `Λ` linear (`Lin`), `Xc b` a column of `X`
gates, `d` diagonal (`A`).  The products of this form contain `1` and are
closed under multiplication on the right by a gate: a phase gate joins `d`;
an `X` gate passes `d` (`A_conj_X`, from `R₁₁`) and joins the column; a
linear gate passes `d` (`A_conj_lin`) and the column (`lin_conj_Xc`) and
joins `Λ`.

**The semantic split** (`nf_unique`, Proposition 6.4).  In operator order
`d` acts first, so the pair of `Λ * Xc b * d` is
`x ↦ ω^{p_d(x)} |Λ(x ⊕ b)⟩`: the phase is that of `d` alone, and the map is
`x ↦ Λ(x ⊕ b)`.  Two normal forms with the same pair therefore have
`Λ(b ⊕ b') = Λ'(0) = 0`, so `b = b'`; then `Λ = Λ'` as maps, and as
elements by linear completeness (`lin_complete`); and `d`, `d'` have the
same phase, so `d = d'` by diagonal completeness (`diag_complete`).

On `0` wires every circuit is a power of `ω`, determined modulo `8` by its
phase (`R₁₀`).
-/
import QCert.CNOTDihedral.Diagonal

namespace QCert.CNOTDihedral

open Circuit

/-- Every generator is one of the gates. -/
theorem gen_cases : ∀ {n : ℕ} (g : Gen Gate n), mk (FreeMonoid.of g) = qω ∨
    ∃ i, mk (FreeMonoid.of g) = qX i ∨ mk (FreeMonoid.of g) = qT i ∨
      mk (FreeMonoid.of g) = qCX i ∨ mk (FreeMonoid.of g) = qSW i
  | _, .gate0 c => by cases c; exact Or.inl rfl
  | _, .gate1 c => by
    cases c
    · exact Or.inr ⟨0, Or.inl rfl⟩
    · exact Or.inr ⟨0, Or.inr (Or.inl rfl)⟩
  | _, .gate2 c => by
    cases c
    · exact Or.inr ⟨0, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact Or.inr ⟨0, Or.inr (Or.inr (Or.inr rfl))⟩
  | _, .gate3 c => nomatch c
  | _, .up g => by
    have e : mk (FreeMonoid.of g.up) = sh (mk (FreeMonoid.of g)) := rfl
    rcases gen_cases g with h | ⟨i, h | h | h | h⟩ <;> rw [e, h]
    · exact Or.inl sh_qω
    · exact Or.inr ⟨i + 1, Or.inl rfl⟩
    · exact Or.inr ⟨i + 1, Or.inr (Or.inl rfl)⟩
    · exact Or.inr ⟨i + 1, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact Or.inr ⟨i + 1, Or.inr (Or.inr (Or.inr rfl))⟩

/-! ### The normal form -/

/-- `q` is `Λ * Xc b * d` with `Λ` linear and `d` diagonal. -/
def NF (n : ℕ) (q : Q (n + 1)) : Prop :=
  ∃ Λ ∈ Lin (n + 1), ∃ b : State 2 (n + 1), ∃ d ∈ A n, q = Λ * Xc b * d

theorem nf_one (n : ℕ) : NF n 1 :=
  ⟨1, (Lin _).one_mem, 0, 1, (A n).one_mem, by rw [Xc_zero]; group⟩

theorem NF_mul_gen {n : ℕ} {q : Q (n + 1)} (hq : NF n q) (g : Gen Gate (n + 1)) :
    NF n (q * mk (FreeMonoid.of g)) := by
  obtain ⟨Λ, hΛ, b, d, hd, rfl⟩ := hq
  rcases gen_cases g with h | ⟨i, h | h | h | h⟩ <;> rw [h]
  · exact ⟨Λ, hΛ, b, d * qω, (A n).mul_mem hd qω_mem_A, by group⟩
  · -- `X`
    refine ⟨Λ, hΛ, b + ei i, qX i * d * qX i, A_conj_X i d hd, ?_⟩
    have hx : Xc b * qX i = Xc (b + ei i) := by
      by_cases hi : i < n + 1
      · rw [← Xc_ei hi, Xc_mul]
      · rw [qX_out (by omega), mul_one]
        congr 1
        funext j; simp [ei, show (j : ℕ) ≠ i by omega]
    rw [← hx]
    calc Λ * Xc b * d * qX i = Λ * Xc b * (qX i * qX i) * d * qX i := by rw [qX_sq, mul_one]
      _ = _ := by group
  · exact ⟨Λ, hΛ, b, d * qT i, (A n).mul_mem hd (qT_mem_A i), by group⟩
  · -- `CNOT`
    have hg : (qCX i : Q (n + 1)) ∈ linGens (n + 1) := ⟨i, Or.inl rfl⟩
    refine ⟨Λ * qCX i, (Lin _).mul_mem hΛ (qCX_mem_Lin i), (paQ (qCX i)).f b,
      qCX i * d * qCX i, A_conj_lin hg d hd, ?_⟩
    have hX := lin_conj_Xc (qCX_mem_Lin (n := n + 1) i) b
    rw [linGens_inv hg] at hX
    rw [← hX]
    calc Λ * Xc b * d * qCX i = Λ * (qCX i * qCX i) * Xc b * (qCX i * qCX i) * d * qCX i := by
          rw [qCX_sq, mul_one, mul_one]
      _ = _ := by group
  · -- `SWAP`
    have hg : (qSW i : Q (n + 1)) ∈ linGens (n + 1) := ⟨i, Or.inr rfl⟩
    refine ⟨Λ * qSW i, (Lin _).mul_mem hΛ (qSW_mem_Lin i), (paQ (qSW i)).f b,
      qSW i * d * qSW i, A_conj_lin hg d hd, ?_⟩
    have hX := lin_conj_Xc (qSW_mem_Lin (n := n + 1) i) b
    rw [linGens_inv hg] at hX
    rw [← hX]
    calc Λ * Xc b * d * qSW i = Λ * (qSW i * qSW i) * Xc b * (qSW i * qSW i) * d * qSW i := by
          rw [qSW_sq, mul_one, mul_one]
      _ = _ := by group

/-- **Every circuit has a normal form** (Proposition 5.5). -/
theorem nf_mk {n : ℕ} (w : Circ (n + 1)) : NF n (mk w) := by
  have h : ∀ l : List (Gen Gate (n + 1)), NF n (mk (FreeMonoid.ofList l)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => exact nf_one n
    | append_singleton l g ih =>
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton]
      exact NF_mul_gen ih g
  have := h (FreeMonoid.toList w)
  rwa [FreeMonoid.ofList_toList] at this

/-! ### Uniqueness: the semantic split -/

theorem state_add_self {n : ℕ} (v : State 2 n) : v + v = 0 := by
  funext j; rcases fin2_cases (v j) with h | h <;> rw [Pi.add_apply, h, Pi.zero_apply] <;> decide

theorem paQ_nf_f {n : ℕ} {Λ : Q (n + 1)} {b : State 2 (n + 1)} {d : Q (n + 1)} (hd : d ∈ A n)
    (s : State 2 (n + 1)) : (paQ (Λ * Xc b * d)).f s = (paQ Λ).f (s + b) := by
  rw [map_mul, map_mul, PA.mul_f, A_f hd, PA.mul_f, paQ_Xc]; rfl

theorem paQ_nf_ph {n : ℕ} {Λ : Q (n + 1)} (hΛ : Λ ∈ Lin (n + 1)) {b : State 2 (n + 1)}
    {d : Q (n + 1)} (s : State 2 (n + 1)) : (paQ (Λ * Xc b * d)).ph s = (paQ d).ph s := by
  rw [map_mul, map_mul, PA.mul_ph, PA.mul_ph, paQ_Xc, (lin_pa hΛ).1]
  simp

/-- **Uniqueness of the normal form** (Proposition 6.4). -/
theorem nf_unique {n : ℕ} {Λ Λ' : Q (n + 1)} (hΛ : Λ ∈ Lin (n + 1)) (hΛ' : Λ' ∈ Lin (n + 1))
    {b b' : State 2 (n + 1)} {d d' : Q (n + 1)} (hd : d ∈ A n) (hd' : d' ∈ A n)
    (h : paQ (Λ * Xc b * d) = paQ (Λ' * Xc b' * d')) : Λ * Xc b * d = Λ' * Xc b' * d' := by
  have hf : ∀ s, (paQ Λ).f (s + b) = (paQ Λ').f (s + b') := fun s => by
    rw [← paQ_nf_f hd, ← paQ_nf_f hd', h]
  have hph : ∀ s, (paQ d).ph s = (paQ d').ph s := fun s => by
    rw [← paQ_nf_ph hΛ (b := b) (d := d) s, ← paQ_nf_ph hΛ' (b := b') (d := d') s, h]
  have z0 : ∀ {M : Q (n + 1)}, M ∈ Lin (n + 1) → (paQ M).f 0 = 0 := fun hM => by
    have := (lin_pa hM).2 0 0; simp only [add_zero] at this
    simpa using this.symm
  -- the columns agree
  have hb : b = b' := by
    have e := hf b
    rw [state_add_self, z0 hΛ] at e
    have e' : (paQ Λ').f (b + b') = (paQ Λ').f 0 := by rw [← e, z0 hΛ']
    have := paQ_f_injective Λ' e'
    calc b = b + (b' + b') := by rw [state_add_self, add_zero]
      _ = (b + b') + b' := by rw [add_assoc]
      _ = b' := by rw [this, zero_add]
  subst hb
  -- the linear parts agree
  have hL : paQ Λ = paQ Λ' := by
    refine PA.ext' (fun t => ?_) (fun t => by rw [(lin_pa hΛ).1, (lin_pa hΛ').1])
    have := hf (t + b)
    rwa [add_assoc, state_add_self, add_zero] at this
  rw [lin_complete (n + 1) hΛ hΛ' hL]
  -- the diagonal parts agree
  have hD : paQ d = paQ d' := PA.ext' (fun s => by rw [A_f hd, A_f hd']) hph
  rw [diag_complete hd hd' hD]

/-! ### Completeness -/

theorem mk_zero_width (w : Circ 0) : mk w = qω ^ (FreeMonoid.length w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    have hg : mk (FreeMonoid.of g) = qω := by
      cases g with
      | gate0 c => cases c; rfl
    rw [map_mul, ih, hg, FreeMonoid.length_mul, FreeMonoid.length_of, add_comm, pow_succ']

theorem paQ_qω_pow {n : ℕ} (k : ℕ) : paQ ((qω : Q n) ^ k) = ⟨id, fun _ => (k : ZMod 8)⟩ := by
  induction k with
  | zero => refine PA.ext' (fun s => rfl) (fun s => ?_); simp
  | succ k ih =>
    rw [pow_succ, map_mul, ih, paQ_qω]
    refine PA.ext' (fun s => rfl) (fun s => ?_)
    simp only [PA.mul_ph, Nat.cast_succ]
    ring

/-- **Completeness for the phase-affine pairs**: circuits with the same
pair are equal in the theory, on every number of wires. -/
theorem complete_pa : ∀ (n : ℕ) {w v : Circ n}, pa n w = pa n v → Eqv n w v
  | 0, w, v, h => by
    rw [← mk_eq_iff, mk_zero_width, mk_zero_width]
    have e : paQ (mk w) = paQ (mk v) := h
    rw [mk_zero_width, mk_zero_width, paQ_qω_pow, paQ_qω_pow] at e
    have e' := congrFun (congrArg PA.ph e) (fun j => j.elim0)
    simp only at e'
    rw [pow_eq_pow_mod _ qω_pow_eight, pow_eq_pow_mod (FreeMonoid.length v) qω_pow_eight,
      (ZMod.natCast_eq_natCast_iff' _ _ _).1 e']
  | n + 1, w, v, h => by
    rw [← mk_eq_iff]
    obtain ⟨Λ, hΛ, b, d, hd, e1⟩ := nf_mk w
    obtain ⟨Λ', hΛ', b', d', hd', e2⟩ := nf_mk v
    have hp : paQ (mk w) = paQ (mk v) := h
    rw [e1, e2] at hp ⊢
    exact nf_unique hΛ hΛ' hd hd' hp

end QCert.CNOTDihedral
