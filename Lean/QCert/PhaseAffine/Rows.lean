/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Linear forms computed by linear circuits

A linear circuit acts linearly (`sem_add`, `sem_smul`), so the first
coordinate of its output is a linear form, `rowv W · x` (`sem_row`).
Conversely every nonzero form is the first coordinate of an explicit linear
circuit, `rowW u` (a multiplier and a fan, or the form one wire up moved
down by a crossing), and every pair of independent forms are the first two
coordinates of `row2W u v`.  With `atom_wd`, a phase gate placed on a form
by these circuits is the phase gate placed on it by any circuit.
-/
import QCert.PhaseAffine.Atom

namespace QCert.PhaseAffine

open Circuit

variable {d lv : ℕ}

local notation "𝒢" => gateData d lv

/-! ### Linearity -/

theorem cons_add' {n : ℕ} (x y : ZMod d) (s t : Lab d n) :
    (Fin.cons x s : Lab d (n + 1)) + Fin.cons y t = Fin.cons (x + y) (s + t) := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

theorem cons_smul' {n : ℕ} (c x : ZMod d) (s : Lab d n) :
    c • (Fin.cons x s : Lab d (n + 1)) = Fin.cons (c * x) (c • s) := by
  funext i; refine Fin.cases rfl (fun j => rfl) i

theorem affMap_add {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) (y z : Lab d n) :
    affMap x (y + z) = affMap x y + affMap x z := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsLin])
  | gate3 g => exact absurd hx (by simp [Gen.IsLin])
  | gate1 g =>
    cases g with
    | M a => simp only [affMap, cons_add', Pi.add_apply, mul_add]; rfl
    | _ => exact absurd hx (by simp [Gen.IsLin])
  | gate2 g =>
    cases g with
    | CX => simp only [affMap, cons_add', Pi.add_apply]; congr 1; ring
    | SWAP => simp only [affMap, cons_add', Pi.add_apply]; rfl
  | up g ih =>
    simp only [affMap]
    rw [cons_add', show Fin.tail (y + z) = Fin.tail y + Fin.tail z from rfl, ih hx]; rfl

theorem affMap_smul {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) (c : ZMod d) (y : Lab d n) :
    affMap x (c • y) = c • affMap x y := by
  induction x with
  | gate0 c' => exact absurd hx (by simp [Gen.IsLin])
  | gate3 g => exact absurd hx (by simp [Gen.IsLin])
  | gate1 g =>
    cases g with
    | M a => simp only [affMap, cons_smul', Pi.smul_apply, smul_eq_mul]; congr 1; ring
    | _ => exact absurd hx (by simp [Gen.IsLin])
  | gate2 g =>
    cases g with
    | CX => simp only [affMap, cons_smul', Pi.smul_apply, smul_eq_mul]; congr 1; ring
    | SWAP => simp only [affMap, cons_smul', Pi.smul_apply, smul_eq_mul]; rfl
  | up g ih =>
    simp only [affMap]
    rw [cons_smul', show Fin.tail (c • y) = c • Fin.tail y from rfl, ih hx]; rfl

theorem gen_isLin_isAff {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsLin) : x.IsAff := by
  induction x with
  | gate0 c => exact absurd hx (by simp [Gen.IsLin])
  | gate1 g => cases g <;> simp_all [Gen.IsLin, Gen.IsAff]
  | gate2 g => trivial
  | gate3 g => nomatch g
  | up g ih => exact ih hx

theorem sem_add {n : ℕ} (w : C d lv n) (hw : IsLinW w) (y z : Lab d n) :
    ((𝒢).sem n w).f (y + z) = ((𝒢).sem n w).f y + ((𝒢).sem n w).f z := by
  induction w using FreeMonoid.inductionOn' generalizing y z with
  | one => rfl
  | mul_of x w ih =>
    obtain ⟨hx, hw'⟩ := IsLinW.of_mul hw
    rw [sem_f_mul, sem_f_mul, sem_f_mul, ih hw', GateData.sem_of]
    simp only [gen_f x (gen_isLin_isAff x hx)]
    exact affMap_add x hx _ _

theorem sem_smul {n : ℕ} (w : C d lv n) (hw : IsLinW w) (c : ZMod d) (y : Lab d n) :
    ((𝒢).sem n w).f (c • y) = c • ((𝒢).sem n w).f y := by
  induction w using FreeMonoid.inductionOn' generalizing y with
  | one => rfl
  | mul_of x w ih =>
    obtain ⟨hx, hw'⟩ := IsLinW.of_mul hw
    rw [sem_f_mul, sem_f_mul, ih hw', GateData.sem_of]
    simp only [gen_f x (gen_isLin_isAff x hx)]
    exact affMap_smul x hx _ _

/-- The first row of a linear circuit. -/
def rowv {n : ℕ} (w : C d lv (n + 1)) : Lab d (n + 1) :=
  fun k => ((𝒢).sem (n + 1) w).f (Pi.single k 1) 0

theorem sem_row {n : ℕ} (w : C d lv (n + 1)) (hw : IsLinW w) (y : Lab d (n + 1)) :
    ((𝒢).sem (n + 1) w).f y 0 = ∑ k, rowv w k * y k := by
  conv_lhs => rw [show y = ∑ k, y k • Pi.single k (1 : ZMod d) by
    funext i; simp [Finset.sum_apply, Pi.single_apply]]
  have hsum : ∀ s : Finset (Fin (n + 1)), ((𝒢).sem (n + 1) w).f (∑ k ∈ s, y k • Pi.single k 1) =
      ∑ k ∈ s, y k • ((𝒢).sem (n + 1) w).f (Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (sem_lin w hw).1
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, sem_add w hw, sem_smul w hw, ih]
  rw [hsum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, rowv]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-! ### A circuit for every linear form -/

section Field

variable [Fact d.Prime]

/-- A linear circuit whose first coordinate is `u · x` (`u ≠ 0`): `M_{u₀}`
after the fan `x₀ ↦ x₀ + (u₀⁻¹ u_{>0}) · x_{>0}` if `u₀ ≠ 0`, and otherwise
the circuit for `u_{>0}` one wire up, moved to wire `0` by the crossing. -/
def rowW : (n : ℕ) → Lab d (n + 1) → C d lv (n + 1)
  | 0, u => g1 (Gate.M (unitOf (u 0)))
  | n + 1, u => if u 0 = 0 then g2 Gate.SWAP * shift (rowW n (Fin.tail u))
      else g1 (Gate.M (unitOf (u 0))) * fanW (n + 1) ((u 0)⁻¹ • Fin.tail u)

theorem isLinW_rowW : ∀ (n : ℕ) (u : Lab d (n + 1)), IsLinW (rowW (lv := lv) n u)
  | 0, _ => isLinW_M _
  | n + 1, u => by
    rw [rowW]; split_ifs
    · exact (isLinW_g2 _).mul (isLinW_shift (isLinW_rowW n _))
    · exact (isLinW_M _).mul (isLinW_fanW _ _)

theorem sum_cons {n : ℕ} (u y : Lab d (n + 1)) :
    ∑ j, u j * y j = u 0 * y 0 + ∑ j, Fin.tail u j * Fin.tail y j := by
  rw [Fin.sum_univ_succ]; rfl

theorem sem_rowW : ∀ (n : ℕ) (u : Lab d (n + 1)), u ≠ 0 → ∀ y : Lab d (n + 1),
    ((𝒢).sem (n + 1) (rowW n u)).f y 0 = ∑ j, u j * y j
  | 0, u, hu, y => by
    rw [rowW, ← Fin.cons_self_tail y, sem_f_M, Fin.cons_zero, Fin.sum_univ_one]
    by_cases h : u 0 = 0
    · exact absurd (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h) hu
    · rw [unitOf_val h]; rfl
  | n + 1, u, hu, y => by
    rw [rowW, sum_cons]
    split_ifs with h
    · have ht : Fin.tail u ≠ 0 := by
        intro ht; apply hu; rw [← Fin.cons_self_tail u, h, ht]
        funext i; refine Fin.cases rfl (fun j => rfl) i
      rw [← Fin.cons_self_tail y, sem_f_mul, sem_f_shift,
        ← Fin.cons_self_tail (((𝒢).sem (n + 1) (rowW n (Fin.tail u))).f (Fin.tail y)),
        sem_f_SW, Fin.cons_zero, Fin.tail_cons, Fin.cons_self_tail, sem_rowW n _ ht, h, zero_mul,
        zero_add]
    · rw [← Fin.cons_self_tail y, sem_f_mul, sem_fanW, sem_f_M, Fin.cons_zero, Fin.cons_zero,
        Fin.tail_cons, unitOf_val h, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

/-! ### A circuit for every pair of independent forms -/

/-- Two independent forms. -/
def Indep {n : ℕ} (u v : Lab d n) : Prop := ∀ a b : ZMod d, a • u + b • v = 0 → a = 0 ∧ b = 0

theorem Indep.symm {n : ℕ} {u v : Lab d n} (h : Indep u v) : Indep v u := fun a b e =>
  (h b a (by rw [add_comm]; exact e)).symm

theorem Indep.ne_zero {n : ℕ} {u v : Lab d n} (h : Indep u v) : u ≠ 0 := by
  intro hu
  have := (h 1 0 (by simp [hu])).1
  exact one_ne_zero this

theorem Indep.add_ne_zero {n : ℕ} {u v : Lab d n} (h : Indep u v) : u + v ≠ 0 := by
  intro e
  have := (h 1 1 (by simpa using e)).1
  exact one_ne_zero this

theorem Indep.sub_ne_zero {n : ℕ} {u v : Lab d n} (h : Indep u v) : u - v ≠ 0 := by
  intro e
  have := (h 1 (-1) (by simpa [sub_eq_add_neg] using e)).1
  exact one_ne_zero this

theorem Indep.neg_right {n : ℕ} {u v : Lab d n} (h : Indep u v) : Indep u (-v) := fun a b e =>
  by
  have := h a (-b) (by simpa using e)
  exact ⟨this.1, neg_eq_zero.1 this.2⟩

/-- A nonzero form and another are proportional or independent. -/
theorem dep_or_indep {n : ℕ} (u v : Lab d n) (hu : u ≠ 0) : (∃ c : ZMod d, v = c • u) ∨ Indep u v := by
  by_cases h : ∃ c : ZMod d, v = c • u
  · exact Or.inl h
  · refine Or.inr fun a b e => ?_
    by_cases hb : b = 0
    · subst hb
      refine ⟨?_, rfl⟩
      by_contra ha
      apply hu
      have : a • u = 0 := by simpa using e
      exact (smul_eq_zero.1 this).resolve_left ha
    · exfalso; apply h
      refine ⟨-(b⁻¹ * a), ?_⟩
      have : b • v = -(a • u) := eq_neg_of_add_eq_zero_right e
      calc v = b⁻¹ • (b • v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, neg_smul]

/-- The `CX` from wire `0` to wire `1`, labelled. -/
def abarW {n : ℕ} (k : ZMod d) : C d lv (n + 2) := g2 Gate.SWAP * g2 Gate.CX ^ k.val * g2 Gate.SWAP

omit [Fact d.Prime] in
theorem isLinW_abarW {n : ℕ} (k : ZMod d) : IsLinW (abarW (d := d) (lv := lv) (n := n) k) :=
  ((isLinW_g2 _).mul ((isLinW_g2 _).pow _)).mul (isLinW_g2 _)

theorem sem_abarW {n : ℕ} (k : ZMod d) (x0 x1 : ZMod d) (r : Lab d n) :
    ((𝒢).sem (n + 2) (abarW k)).f (Fin.cons x0 (Fin.cons x1 r)) =
      Fin.cons x0 (Fin.cons (x1 + k * x0) r) := by
  rw [abarW, sem_f_mul, sem_f_mul, sem_f_SW, sem_f_CX_pow, sem_f_SW, ZMod.natCast_zmod_val]

/-- The two forms `u` (with `u₀ ≠ 0`) and `v`, by the circuit for `u`, the
circuit for `v_{>0} - λ u_{>0}` one wire up, and `CX^λ` from wire `0` to wire
`1`, `λ = v₀ / u₀`. -/
def row2A (n : ℕ) (u v : Lab d (n + 2)) : C d lv (n + 2) :=
  abarW (v 0 * (u 0)⁻¹) * shift (rowW n (Fin.tail v - (v 0 * (u 0)⁻¹) • Fin.tail u)) *
    rowW (n + 1) u

/-- A linear circuit whose first two coordinates are `u · x` and `v · x`
(`u`, `v` independent): `row2A` if `u₀ ≠ 0`, the same for `v, u` then the
crossing if `v₀ ≠ 0`, and otherwise the pair one wire up, moved to the wires
`0, 1` by two crossings. -/
def row2W : (n : ℕ) → Lab d (n + 2) → Lab d (n + 2) → C d lv (n + 2)
  | 0, u, v => if u 0 ≠ 0 then row2A 0 u v else g2 Gate.SWAP * row2A 0 v u
  | n + 1, u, v =>
    if u 0 ≠ 0 then row2A (n + 1) u v
    else if v 0 ≠ 0 then g2 Gate.SWAP * row2A (n + 1) v u
    else shift (g2 Gate.SWAP) * g2 Gate.SWAP * shift (row2W n (Fin.tail u) (Fin.tail v))

theorem isLinW_row2A (n : ℕ) (u v : Lab d (n + 2)) : IsLinW (row2A (lv := lv) n u v) :=
  ((isLinW_abarW _).mul (isLinW_shift (isLinW_rowW _ _))).mul (isLinW_rowW _ _)

theorem isLinW_row2W : ∀ (n : ℕ) (u v : Lab d (n + 2)), IsLinW (row2W (lv := lv) n u v)
  | 0, u, v => by
    rw [row2W]; split_ifs
    · exact isLinW_row2A _ _ _
    · exact (isLinW_g2 _).mul (isLinW_row2A _ _ _)
  | n + 1, u, v => by
    rw [row2W]; split_ifs
    · exact isLinW_row2A _ _ _
    · exact (isLinW_g2 _).mul (isLinW_row2A _ _ _)
    · exact ((isLinW_shift (isLinW_g2 _)).mul (isLinW_g2 _)).mul
        (isLinW_shift (isLinW_row2W n _ _))

theorem sem_rowW_full (n : ℕ) (u : Lab d (n + 2)) (h : u 0 ≠ 0) (y : Lab d (n + 2)) :
    ((𝒢).sem (n + 2) (rowW (n + 1) u)).f y = Fin.cons (∑ j, u j * y j) (Fin.tail y) := by
  have h0 := sem_rowW (lv := lv) (n + 1) u (fun e => h (by rw [e]; rfl)) y
  rw [rowW, if_neg h] at h0 ⊢
  rw [← Fin.cons_self_tail y, sem_f_mul, sem_fanW, sem_f_M] at h0 ⊢
  rw [Fin.cons_zero] at h0
  rw [h0, Fin.tail_cons]

theorem Indep.tail {n : ℕ} {u v : Lab d (n + 1)} (h : Indep u v) (hu : u 0 = 0) (hv : v 0 = 0) :
    Indep (Fin.tail u) (Fin.tail v) := by
  intro a b e
  apply h a b
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hu, hv]
  · have := congrFun e j
    simpa [Fin.tail] using this

theorem sem_row2A (n : ℕ) (u v : Lab d (n + 2)) (hu : u 0 ≠ 0) (h : Indep u v)
    (y : Lab d (n + 2)) :
    ((𝒢).sem (n + 2) (row2A n u v)).f y 0 = ∑ j, u j * y j ∧
      ((𝒢).sem (n + 2) (row2A n u v)).f y 1 = ∑ j, v j * y j := by
  set c := v 0 * (u 0)⁻¹
  set w := Fin.tail v - c • Fin.tail u
  have hw : w ≠ 0 := by
    intro hw0
    have key : v = c • u := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · show v 0 = v 0 * (u 0)⁻¹ * u 0
        rw [mul_assoc, inv_mul_cancel₀ hu, mul_one]
      · have := congrFun hw0 j
        simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        exact sub_eq_zero.1 this
    have := (h c (-1) (by rw [key]; simp)).2
    exact one_ne_zero (neg_eq_zero.1 this)
  have hR := sem_rowW_full (lv := lv) n u hu y
  rw [← Fin.cons_self_tail y] at hR ⊢
  rw [row2A, sem_f_mul, sem_f_mul, hR, Fin.tail_cons, sem_f_shift,
    ← Fin.cons_self_tail (((𝒢).sem (n + 1) (rowW n w)).f (Fin.tail y)), sem_abarW,
    sem_rowW n w hw]
  refine ⟨?_, ?_⟩
  · simp only [Fin.cons_zero]
  · simp only [Fin.cons_one, Fin.cons_zero, sum_cons u (Fin.cons (y 0) (Fin.tail y)),
      sum_cons v (Fin.cons (y 0) (Fin.tail y)), Fin.tail_cons]
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum, c]
    field_simp
    ring

omit [Fact d.Prime] in
theorem sem_of_mul_f {n : ℕ} (x : Gen (Gate d lv) n) (hx : x.IsAff) (V : C d lv n)
    (y : Lab d n) :
    ((𝒢).sem n (FreeMonoid.of x * V)).f y = affMap x (((𝒢).sem n V).f y) := by
  rw [sem_f_mul, GateData.sem_of, gen_f x hx]

omit [Fact d.Prime] in
theorem sem_SW_mul {n : ℕ} (V : C d lv (n + 2)) (y : Lab d (n + 2)) :
    ((𝒢).sem (n + 2) (g2 Gate.SWAP * V)).f y 0 = ((𝒢).sem (n + 2) V).f y 1 ∧
      ((𝒢).sem (n + 2) (g2 Gate.SWAP * V)).f y 1 = ((𝒢).sem (n + 2) V).f y 0 := by
  rw [show (g2 Gate.SWAP * V : C d lv (n + 2)) = FreeMonoid.of (Gen.gate2 Gate.SWAP) * V from rfl,
    sem_of_mul_f _ (by exact trivial)]
  simp [affMap]

theorem sem_row2W : ∀ (n : ℕ) (u v : Lab d (n + 2)), Indep u v → ∀ y : Lab d (n + 2),
    ((𝒢).sem (n + 2) (row2W n u v)).f y 0 = ∑ j, u j * y j ∧
      ((𝒢).sem (n + 2) (row2W n u v)).f y 1 = ∑ j, v j * y j
  | 0, u, v, h, y => by
    rw [row2W]
    split_ifs with hu
    · exact sem_row2A 0 u v hu h y
    · have hv : v 0 ≠ 0 := by
        intro hv
        apply h.ne_zero
        have := (h (v 1) (-u 1) (by
          funext i; fin_cases i
          · simp [not_not.1 hu, hv]
          · simp [mul_comm])).2
        funext i; fin_cases i
        · exact not_not.1 hu
        · simpa using this
      have := sem_row2A (lv := lv) 0 v u hv h.symm y
      have hs := sem_SW_mul (row2A (lv := lv) 0 v u) y
      exact ⟨hs.1.trans this.2, hs.2.trans this.1⟩
  | n + 1, u, v, h, y => by
    rw [row2W]
    split_ifs with hu hv
    · exact sem_row2A (n + 1) u v hu h y
    · have := sem_row2A (lv := lv) (n + 1) v u hv h.symm y
      have hs := sem_SW_mul (row2A (lv := lv) (n + 1) v u) y
      exact ⟨hs.1.trans this.2, hs.2.trans this.1⟩
    · have hu' := not_not.1 hu
      have hv' := not_not.1 hv
      have ih := sem_row2W n (Fin.tail u) (Fin.tail v) (h.tail hu' hv') (Fin.tail y)
      set R := row2W (lv := lv) n (Fin.tail u) (Fin.tail v)
      set z := ((𝒢).sem (n + 2) R).f (Fin.tail y)
      have hsh : ((𝒢).sem (n + 3) (shift R)).f y = Fin.cons (y 0) z := by
        conv_lhs => rw [← Fin.cons_self_tail y]
        rw [sem_f_shift]
      rw [show (shift (g2 Gate.SWAP) * g2 Gate.SWAP * shift R : C d lv (n + 3)) =
          FreeMonoid.of (Gen.up (Gen.gate2 Gate.SWAP)) *
            (FreeMonoid.of (Gen.gate2 Gate.SWAP) * shift R) by rw [← shift_of, mul_assoc],
        sem_of_mul_f _ (by exact trivial), sem_of_mul_f _ (by exact trivial), hsh]
      rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail (Fin.tail z)] at ih ⊢
      simp only [affMap, Fin.cons_zero, Fin.cons_one, Fin.tail_cons] at ih ⊢
      rw [sum_cons u, sum_cons v, hu', hv']
      simp only [zero_mul, zero_add]
      exact ⟨ih.1, ih.2⟩

end Field

end QCert.PhaseAffine
