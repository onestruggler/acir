/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Weyl operators and their conjugation by circuits

The Weyl operator of `v : V p n`, `v i = (aᵢ, bᵢ)`, is
`weylOp v = ⊗ᵢ X^{aᵢ} Z^{bᵢ}`, the monomial operator
`|t⟩ ↦ ψ(Σᵢ bᵢ tᵢ) |t + a⟩` (digitwise addition).  `WeylActs U f` says that
`U` conjugates every Weyl operator `weylOp v` to a nonzero multiple of
`weylOp (f v)`:

* `H`, `S` and `CZ` act on their own wires by `act1` and the `CZ` rule of
  `σGen` (`weylActs_H`, `weylActs_S`, `weylActs_CZ`), with phases
  `ψ(-ab)`, `ψ(q a)` and `ψ(a₀ a₁)`;
* a Weyl operator on `n + k` wires is one on the bottom `k` wires times one
  on the top `n` (`weylOp_split`), so a gate on the bottom wires and a
  generator moved up act as on their own wires (`WeylActs.onBottom`,
  `WeylActs.onTop`);
* so every circuit acts by its symplectic action `σC` (`weylActs_sem`).

Weyl operators of distinct vectors are not proportional
(`weylOp_eq_smul`): their supports differ, or their phases at a basis
vector do.
-/
import QCert.QuditClifford.SymplecticDef
import QCert.QuditClifford.Rules

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

/-! ### The character and translations of digits -/

theorem weyl_ψ_ne_zero (a : ZMod p) : ψ p a ≠ 0 :=
  pow_ne_zero _ ((ωℂ_primitive p).ne_zero hp.out.ne_zero)

theorem weyl_ψ_injective : Function.Injective (ψ p) := fun a b h =>
  ZMod.val_injective p ((ωℂ_primitive p).pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

/-- The digit `y` translated by `x ∈ ℤ_p`. -/
def wtr (x : ZMod p) (y : Fin p) : Fin p := zinv p (z p y + x)

theorem z_wtr (x : ZMod p) (y : Fin p) : z p (wtr p x y) = z p y + x := z_zinv p _

theorem wtr_neg_wtr (x : ZMod p) (y : Fin p) : wtr p (-x) (wtr p x y) = y :=
  z_injective p (by rw [z_wtr, z_wtr]; ring)

theorem wtr_wtr_neg (x : ZMod p) (y : Fin p) : wtr p x (wtr p (-x) y) = y :=
  z_injective p (by rw [z_wtr, z_wtr]; ring)

/-- Products of characters, as their exponents. -/
theorem weyl_key2 {A B C D E : ZMod p} (h : A + B = C + (D + E)) :
    ψ p A * ψ p B = ψ p C * (ψ p D * ψ p E) := by
  calc ψ p A * ψ p B = ψ p (A + B) := (ψ_add p A B).symm
    _ = ψ p (C + (D + E)) := by rw [h]
    _ = ψ p C * (ψ p D * ψ p E) := by rw [ψ_add p C, ψ_add p D]

theorem weyl_key3 (c : ℂ) {A B C D E : ZMod p} (h : A + B = C + (D + E)) :
    c * ψ p A * ψ p B = ψ p C * (ψ p D * (c * ψ p E)) := by
  rw [mul_assoc, weyl_key2 p h]; ring

/-! ### Products with monomial operators -/

omit hp in
theorem weyl_mul_mono_apply {n : ℕ} (A : Op ℂ p n) (σ : State p n → State p n)
    (φ : State p n → ℂ) (s t : State p n) : (A * mono p σ φ) s t = A s (σ t) * φ t := by
  rw [mul_apply, Finset.sum_eq_single (σ t)]
  · simp [mono]
  · intro u _ hu; simp [mono, hu]
  · simp

omit hp in
theorem weyl_mono_mul_apply {n : ℕ} {σ τ : State p n → State p n} (h1 : ∀ s, σ (τ s) = s)
    (h2 : ∀ u, τ (σ u) = u) (φ : State p n → ℂ) (A : Op ℂ p n) (s t : State p n) :
    (mono p σ φ * A) s t = φ (τ s) * A (τ s) t := by
  rw [mul_apply, Finset.sum_eq_single (τ s)]
  · simp [mono, h1]
  · intro u _ hu
    have hs : s ≠ σ u := fun e => hu (by rw [e, h2])
    simp [mono, hs]
  · simp

/-! ### Weyl operators -/

/-- The Weyl operator `⊗ᵢ X^{aᵢ} Z^{bᵢ}`, `v i = (aᵢ, bᵢ)`:
`|t⟩ ↦ ψ(Σᵢ bᵢ tᵢ) |t + a⟩`. -/
def weylOp {n : ℕ} (v : V p n) : Op ℂ p n :=
  mono p (fun t i => wtr p (v i).1 (t i)) fun t => ψ p (∑ i, (v i).2 * z p (t i))

theorem weylOp_def {n : ℕ} (v : V p n) :
    weylOp p v = mono p (fun t i => wtr p (v i).1 (t i)) fun t => ψ p (∑ i, (v i).2 * z p (t i)) :=
  rfl

theorem weylOp_apply {n : ℕ} (v : V p n) (s t : State p n) :
    weylOp p v s t =
      if s = (fun i => wtr p (v i).1 (t i)) then ψ p (∑ i, (v i).2 * z p (t i)) else 0 :=
  rfl

theorem mul_weylOp_apply {n : ℕ} (A : Op ℂ p n) (v : V p n) (s t : State p n) :
    (A * weylOp p v) s t =
      A s (fun i => wtr p (v i).1 (t i)) * ψ p (∑ i, (v i).2 * z p (t i)) :=
  weyl_mul_mono_apply p A _ _ s t

theorem weylOp_mul_apply {n : ℕ} (v : V p n) (A : Op ℂ p n) (s t : State p n) :
    (weylOp p v * A) s t = ψ p (∑ i, (v i).2 * z p (wtr p (-(v i).1) (s i))) *
      A (fun i => wtr p (-(v i).1) (s i)) t :=
  weyl_mono_mul_apply p (σ := fun t i => wtr p (v i).1 (t i))
    (τ := fun s i => wtr p (-(v i).1) (s i))
    (fun s => funext fun i => wtr_wtr_neg p (v i).1 (s i))
    (fun u => funext fun i => wtr_neg_wtr p (v i).1 (u i)) _ A s t

/-! ### Splitting the wires -/

/-- The bottom `k` wires of a vector on `n + k` wires. -/
def weylLo {n k : ℕ} (v : V p (n + k)) : V p k := fun i => v ⟨i, by omega⟩

/-- The top `n` wires of a vector on `n + k` wires. -/
def weylHi {n k : ℕ} (v : V p (n + k)) : V p n := fun j => v ⟨k + j, by omega⟩

theorem weyl_sum_split {M : Type*} [AddCommMonoid M] {n k : ℕ} (f : Fin (n + k) → M) :
    ∑ j, f j = ∑ i : Fin k, f ⟨i, by omega⟩ + ∑ j : Fin n, f ⟨k + j, by omega⟩ :=
  (Fintype.sum_equiv (finCongr (Nat.add_comm n k)) f
    (fun j : Fin (k + n) => f (Fin.cast (Nat.add_comm k n) j)) (fun _ => rfl)).trans
    (Fin.sum_univ_add (fun j : Fin (k + n) => f (Fin.cast (Nat.add_comm k n) j)))

/-- A Weyl operator on `n + k` wires is one on the bottom `k` wires times
one on the top `n`. -/
theorem weylOp_split {n k : ℕ} (v : V p (n + k)) :
    weylOp p v = onBottom (n := n) (weylOp p (weylLo p v)) * onTop k (weylOp p (weylHi p v)) := by
  rw [weylOp_def, weylOp_def, weylOp_def, onBottom_mono, onTop_mono, mono_mul]
  apply mono_ext p
  · intro t
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact (Equiv.eq_symm_apply _).2 rfl
  · intro t
    simp only [Equiv.apply_symm_apply]
    exact (congrArg (ψ p) (weyl_sum_split _)).trans (ψ_add p _ _)

/-! ### Conjugating Weyl operators -/

/-- `U` conjugates each Weyl operator `weylOp v` to a nonzero multiple of
`weylOp (f v)`. -/
def WeylActs {n : ℕ} (U : Op ℂ p n) (f : V p n → V p n) : Prop :=
  ∀ v, ∃ c : ℂ, c ≠ 0 ∧ U * weylOp p v = c • (weylOp p (f v) * U)

theorem weylActs_one {n : ℕ} : WeylActs p (1 : Op ℂ p n) id := fun v =>
  ⟨1, one_ne_zero, by simp only [one_mul, one_smul, mul_one, id_eq]⟩

theorem weylActs_scalar {n : ℕ} (c : ℂ) : WeylActs p (c • (1 : Op ℂ p n)) id := fun v =>
  ⟨1, one_ne_zero, by
    simp only [one_smul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, id_eq]⟩

theorem WeylActs.mul {n : ℕ} {U U' : Op ℂ p n} {f f' : V p n → V p n}
    (h : WeylActs p U f) (h' : WeylActs p U' f') : WeylActs p (U * U') (f ∘ f') := by
  intro v
  obtain ⟨c', hc', e'⟩ := h' v
  obtain ⟨c, hc, e⟩ := h (f' v)
  refine ⟨c' * c, mul_ne_zero hc' hc, ?_⟩
  calc U * U' * weylOp p v = U * (U' * weylOp p v) := mul_assoc _ _ _
    _ = U * (c' • (weylOp p (f' v) * U')) := by rw [e']
    _ = c' • (U * weylOp p (f' v) * U') := by rw [mul_smul_comm, mul_assoc]
    _ = c' • (c • (weylOp p (f (f' v)) * U) * U') := by rw [e]
    _ = (c' * c) • (weylOp p (f (f' v)) * (U * U')) := by
      rw [smul_mul_assoc, smul_smul, mul_assoc]

/-- A conjugation on `k` wires, placed on the bottom `k` of `n + k` wires. -/
theorem WeylActs.onBottom {n k : ℕ} {G : Op ℂ p k} {f : V p k → V p k} (h : WeylActs p G f)
    {F : V p (n + k) → V p (n + k)} (hlo : ∀ v, weylLo p (F v) = f (weylLo p v))
    (hhi : ∀ v, weylHi p (F v) = weylHi p v) : WeylActs p (onBottom (n := n) G) F := by
  intro v
  obtain ⟨c, hc, e⟩ := h (weylLo p v)
  refine ⟨c, hc, ?_⟩
  rw [weylOp_split p v, weylOp_split p (F v), hlo, hhi, ← mul_assoc, ← onBottom_mul, e,
    onBottom_smul, onBottom_mul, smul_mul_assoc, mul_assoc, mul_assoc, onBottom_onTop_comm]

/-- A conjugation on `n` wires, moved up onto the top `n` of `n + k` wires. -/
theorem WeylActs.onTop {n k : ℕ} {M : Op ℂ p n} {f : V p n → V p n} (h : WeylActs p M f)
    {F : V p (n + k) → V p (n + k)} (hlo : ∀ v, weylLo p (F v) = weylLo p v)
    (hhi : ∀ v, weylHi p (F v) = f (weylHi p v)) : WeylActs p (onTop k M) F := by
  intro v
  obtain ⟨c, hc, e⟩ := h (weylHi p v)
  refine ⟨c, hc, ?_⟩
  rw [weylOp_split p v, weylOp_split p (F v), hlo, hhi, ← mul_assoc, ← onBottom_onTop_comm,
    mul_assoc, ← onTop_mul, e, onTop_smul, onTop_mul, mul_smul_comm, ← mul_assoc]

/-! ### The gates on their own wires -/

/-- The action of a one-wire gate on one wire. -/
def weylF1 (h : Gate 1) (u : V p 1) : V p 1 := fun _ => act1 p h (u 0)

theorem weylF1_H (u : V p 1) (i : Fin 1) : weylF1 p Gate.H u i = (-(u 0).2, (u 0).1) := rfl

theorem weylF1_S (u : V p 1) (i : Fin 1) :
    weylF1 p Gate.S u i = ((u 0).1, (u 0).1 + (u 0).2) := rfl

/-- The action of `CZ` on two wires. -/
def weylFCZ (u : V p 2) : V p 2 :=
  ![((u 0).1, (u 0).2 + (u 1).1), ((u 1).1, (u 1).2 + (u 0).1)]

theorem weylFCZ_zero (u : V p 2) : weylFCZ p u 0 = ((u 0).1, (u 0).2 + (u 1).1) := rfl

theorem weylFCZ_one (u : V p 2) : weylFCZ p u 1 = ((u 1).1, (u 1).2 + (u 0).1) := rfl

/-- `H W(a, b) = ψ(-ab) W(-b, a) H`. -/
theorem weylActs_H : WeylActs p (Hop p) (weylF1 p Gate.H) := by
  intro u
  refine ⟨ψ p (-((u 0).1 * (u 0).2)), weyl_ψ_ne_zero p _, ?_⟩
  ext s t
  rw [smul_apply, smul_eq_mul, mul_weylOp_apply, weylOp_mul_apply, Hop_apply, Hop_apply]
  exact weyl_key3 p _ (by simp only [Fin.sum_univ_one, weylF1_H, z_wtr]; ring)

/-- `S W(a, b) = ψ(q a) W(a, a + b) S`. -/
theorem weylActs_S (hp2 : p ≠ 2) : WeylActs p (Sop p) (weylF1 p Gate.S) := by
  intro u
  refine ⟨ψ p (q p (u 0).1), weyl_ψ_ne_zero p _, ?_⟩
  rw [Sop_mono p hp2, weylOp_def, weylOp_def, mono_mul, mono_mul, smul_mono]
  apply mono_ext p
  · intro t
    funext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    rfl
  · intro t
    exact weyl_key2 p (by
      simp only [Fin.sum_univ_one, weylF1_S, z_wtr, id_eq]
      linear_combination q_add p hp2 (z p (t 0)) (u 0).1)

/-- `CZ W(u) = ψ(a₀ a₁) W(fCZ u) CZ`. -/
theorem weylActs_CZ : WeylActs p (CZop p) (weylFCZ p) := by
  intro u
  refine ⟨ψ p ((u 0).1 * (u 1).1), weyl_ψ_ne_zero p _, ?_⟩
  rw [CZop_mono p, weylOp_def, weylOp_def, mono_mul, mono_mul, smul_mono]
  apply mono_ext p
  · intro t
    funext i
    fin_cases i <;> rfl
  · intro t
    exact weyl_key2 p (by
      simp only [Fin.sum_univ_two, weylFCZ_zero, weylFCZ_one, z_wtr, id_eq]
      ring)

/-! ### The generators -/

theorem weyl_mk_ne_zero {m i : ℕ} (hi : i < m + 1) (h0 : i ≠ 0) :
    (⟨i, hi⟩ : Fin (m + 1)) ≠ 0 :=
  fun e => h0 (congrArg Fin.val e)

theorem weyl_mk_ne_zero₂ {m i : ℕ} (hi : i < m + 2) (h0 : i ≠ 0) :
    (⟨i, hi⟩ : Fin (m + 2)) ≠ 0 :=
  fun e => h0 (congrArg Fin.val e)

theorem weyl_mk_ne_one {m i : ℕ} (hi : i < m + 2) (h1 : i ≠ 1) :
    (⟨i, hi⟩ : Fin (m + 2)) ≠ 1 :=
  fun e => h1 (congrArg Fin.val e)

theorem weylLo_gate1 {n : ℕ} (h : Gate 1) (v : V p (n + 1)) :
    weylLo p (k := 1) (σGen p (Gen.gate1 h) v) = weylF1 p h (weylLo p (k := 1) v) := by
  funext i
  fin_cases i
  rfl

theorem weylHi_gate1 {n : ℕ} (h : Gate 1) (v : V p (n + 1)) :
    weylHi p (k := 1) (σGen p (Gen.gate1 h) v) = weylHi p (k := 1) v := by
  funext j
  exact Function.update_of_ne
    (weyl_mk_ne_zero (m := n) (i := 1 + j.val) (by omega) (by omega)) _ _

theorem weylLo_CZ {n : ℕ} (v : V p (n + 2)) :
    weylLo p (k := 2) (σGen p (Gen.gate2 Gate.CZ) v) = weylFCZ p (weylLo p (k := 2) v) := by
  funext i
  fin_cases i <;> rfl

theorem weylHi_CZ {n : ℕ} (v : V p (n + 2)) :
    weylHi p (k := 2) (σGen p (Gen.gate2 Gate.CZ) v) = weylHi p (k := 2) v := by
  funext j
  show Function.update (Function.update v 0 ((v 0).1, (v 0).2 + (v 1).1)) 1
      ((v 1).1, (v 1).2 + (v 0).1) ⟨2 + j.val, by omega⟩ = v ⟨2 + j.val, by omega⟩
  rw [Function.update_of_ne (weyl_mk_ne_one (m := n) (i := 2 + j.val) (by omega) (by omega)),
    Function.update_of_ne (weyl_mk_ne_zero₂ (m := n) (i := 2 + j.val) (by omega) (by omega))]

theorem weyl_σGen_up {n : ℕ} (g : Gen Gate n) (v : V p (n + 1)) :
    σGen p (Gen.up g) v = Fin.cons (v 0) (σGen p g (Fin.tail v)) :=
  rfl

theorem weylLo_up {n : ℕ} (g : Gen Gate n) (v : V p (n + 1)) :
    weylLo p (k := 1) (σGen p (Gen.up g) v) = weylLo p (k := 1) v := by
  funext i
  fin_cases i
  rfl

theorem weylHi_up {n : ℕ} (g : Gen Gate n) (v : V p (n + 1)) :
    weylHi p (k := 1) (σGen p (Gen.up g) v) = σGen p g (weylHi p (k := 1) v) := by
  have ht : Fin.tail v = weylHi p (k := 1) v := by
    funext j
    exact congrArg v (Fin.ext (by simp only [Fin.val_succ]; omega))
  funext j
  have hj : (⟨1 + j.val, by omega⟩ : Fin (n + 1)) = j.succ :=
    Fin.ext (by simp only [Fin.val_succ]; omega)
  show σGen p (Gen.up g) v ⟨1 + j.val, by omega⟩ = _
  rw [weyl_σGen_up, hj, Fin.cons_succ, ht]

/-- Every generator acts on Weyl operators by its symplectic action. -/
theorem weylActs_gen (hp2 : p ≠ 2) {n : ℕ} (g : Gen Gate n) :
    WeylActs p ((gateSem p).gen g : Op ℂ p n) (σGen p g) := by
  induction g with
  | gate0 c =>
    cases c
    exact weylActs_scalar p _
  | gate1 h =>
    cases h
    · exact WeylActs.onBottom p (weylActs_H p) (weylLo_gate1 p Gate.H) (weylHi_gate1 p Gate.H)
    · exact WeylActs.onBottom p (weylActs_S p hp2) (weylLo_gate1 p Gate.S)
        (weylHi_gate1 p Gate.S)
  | gate2 h =>
    cases h
    exact WeylActs.onBottom p (weylActs_CZ p) (weylLo_CZ p) (weylHi_CZ p)
  | gate3 h => cases h
  | up g ih => exact WeylActs.onTop p (k := 1) ih (weylLo_up p g) (weylHi_up p g)

/-- **Every circuit acts on Weyl operators by its symplectic action**:
`sem w · W(v) = c · W(σC w v) · sem w` with `c ≠ 0`. -/
theorem weylActs_sem (hp2 : p ≠ 2) {n : ℕ} (w : Circ n) :
    WeylActs p (sem p n w : Op ℂ p n) (σC p n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    have h1 : ((sem p n 1 : unitaryGroup (State p n) ℂ) : Op ℂ p n) = 1 :=
      (congrArg Subtype.val (map_one (sem p n))).trans rfl
    have h2 : σC p n 1 = id := (map_one (σC p n)).trans rfl
    rw [h1, h2]
    exact weylActs_one p
  | mul_of g w ih =>
    rw [map_mul, map_mul, Submonoid.coe_mul, σC_of]
    exact WeylActs.mul p (weylActs_gen p hp2 g) ih

/-! ### Weyl operators of distinct vectors are not proportional -/

theorem weyl_sum_single {n : ℕ} (f : Fin n → ZMod p) (j : Fin n) :
    ∑ i, f i * (Pi.single j 1 : Fin n → ZMod p) i = f j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, mul_zero]
  · simp

/-- **Weyl operators of distinct vectors are not proportional.** -/
theorem weylOp_eq_smul {n : ℕ} {a b : V p n} {d : ℂ} (h : weylOp p a = d • weylOp p b) :
    a = b := by
  have key : ∀ c : Fin n → ZMod p, (∀ i, (a i).1 = (b i).1) ∧
      ψ p (∑ i, (a i).2 * c i) = d * ψ p (∑ i, (b i).2 * c i) := by
    intro c
    have e := congrFun (congrFun h (fun i => wtr p (a i).1 (zinv p (c i))))
      (fun i => zinv p (c i))
    rw [smul_apply, smul_eq_mul, weylOp_apply, weylOp_apply, if_pos rfl] at e
    by_cases hs : (fun i => wtr p (a i).1 (zinv p (c i))) = fun i => wtr p (b i).1 (zinv p (c i))
    · rw [if_pos hs] at e
      refine ⟨fun i => ?_, ?_⟩
      · have := congrArg (z p) (congrFun hs i)
        simp only [z_wtr] at this
        exact add_left_cancel this
      · simpa only [z_zinv] using e
    · rw [if_neg hs, mul_zero] at e
      exact absurd e (weyl_ψ_ne_zero p _)
  have hd : d = 1 := by
    have h0 := (key 0).2
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, ψ_zero, mul_one] at h0
    exact h0.symm
  funext j
  refine Prod.ext ((key 0).1 j) ?_
  have h1 := (key (Pi.single j 1)).2
  rw [hd, one_mul, weyl_sum_single, weyl_sum_single] at h1
  exact weyl_ψ_injective p h1

end

end QCert.QuditClifford
