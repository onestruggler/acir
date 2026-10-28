/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness for linear circuits

Linear circuits (`CNOT`s and swaps) with the same linear map are equal in
the theory, on every number of wires (`lin_complete`).  This is the part of
the paper's Lemma 5.4 that it takes from Lafont; here it is proved by
induction on the number of wires, with a normal form of Lafont's kind.

**Normal form.**  On `n + 1` wires every linear element is
`sh h * fo c * R r` (`lin_nf`): `h` linear on the upper `n` wires, `fo c`
a fan-out from wire `0`, and `R r` the *row representative* of a nonzero
row `r`, a linear circuit whose output on wire `0` is `r · x`:

* `R r = fi r̄` (a fan-in into wire `0`) if `r₀ = 1`;
* `R r = SW₀₁ * sh (R r̄)` if `r₀ = 0` (the row moved down from wire `1`).

The products `sh h * fo c * R r` contain `1` and are closed under
multiplication on the right by a generator (`R_mul_gen`, eleven cases, each
checked numerically first), since a fan-out passes an upper linear element
(`fo_push`).

**Uniqueness.**  The output on wire `0` is `r · x`, so `r` is determined;
cancelling `R r`, the image of `e₀` determines `c`, and then `h` has the
same linear map as `h'` one wire up, and is equal to it by induction.
-/
import QCert.CNOTDihedral.Fans

namespace QCert.CNOTDihedral

open Circuit

/-! ### The row representatives -/

/-- The row representative: a linear circuit whose output on wire `0` is
`r · x`. -/
noncomputable def R : {n : ℕ} → State 2 (n + 1) → Q (n + 1)
  | 0, _ => 1
  | _ + 1, r => if r 0 = 1 then fi (Fin.tail r) else qSW 0 * sh (R (Fin.tail r))

theorem R_cons_one {n : ℕ} (t : State 2 n) : R (Fin.cons 1 t : State 2 (n + 1)) = fi t := by
  cases n with
  | zero => rfl
  | succ n => simp [R]

theorem R_cons_zero {n : ℕ} (t : State 2 (n + 1)) :
    R (Fin.cons 0 t : State 2 (n + 2)) = qSW 0 * sh (R t) := by
  simp [R]

theorem R_mem_Lin : ∀ {n : ℕ} (r : State 2 (n + 1)), R r ∈ Lin (n + 1)
  | 0, _ => (Lin 1).one_mem
  | n + 1, r => by
    unfold R
    split_ifs
    · exact fi_mem_Lin _
    · exact (Lin _).mul_mem (qSW_mem_Lin 0) (sh_mem_Lin (R_mem_Lin _))

theorem cons_ne_zero_one {n : ℕ} (t : State 2 n) : (Fin.cons 1 t : State 2 (n + 1)) ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

theorem cons_ne_zero {n : ℕ} {t : State 2 n} (ht : t ≠ 0) (a : Fin 2) :
    (Fin.cons a t : State 2 (n + 1)) ≠ 0 := by
  intro h; apply ht; funext j; have := congrFun h j.succ; simpa using this

theorem tail_ne_zero {n : ℕ} {r : State 2 (n + 1)} (hr : r ≠ 0) (h0 : r 0 = 0) :
    Fin.tail r ≠ 0 := by
  intro h; apply hr; funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact h0
  · exact congrFun h j

/-- The output of `R r` on wire `0` is `r · x`. -/
theorem bit_R : ∀ {n : ℕ} (r : State 2 (n + 1)), r ≠ 0 → ∀ s : State 2 (n + 1),
    bit ((paQ (R r)).f s) 0 = dot r s
  | 0, r, hr, s => by
    have h1 : r 0 = 1 := by
      rcases fin2_cases (r 0) with h | h
      · exact absurd (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h) hr
      · exact h
    simp [R, dot, h1, bit]
  | n + 1, r, hr, s => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, r = Fin.cons a t := ⟨r 0, Fin.tail r, (Fin.cons_self_tail r).symm⟩
    rw [← Fin.cons_self_tail s, dot_cons]
    rcases fin2_cases a with rfl | rfl
    · have ht : t ≠ 0 := by
        have := tail_ne_zero hr (by simp); simpa using this
      rw [R_cons_zero, map_mul, PA.mul_f, Function.comp_apply, paQ_qSW]
      simp only
      rw [bit_comp_swq _ (by omega), if_pos rfl, paQ_sh_f, bit_cons_succ, Fin.tail_cons,
        bit_R t ht]
      simp
    · rw [R_cons_one, bit_fi_zero]
      simp [Fin.tail_cons, bit]

/-! ### Fans past linear generators one wire up -/

theorem cc_eq_fo {n : ℕ} (j : Fin n) : (cc 0 (j.val + 1) : Q (n + 1)) = fo (Pi.single j 1) :=
  (cprod_single (fun j : Fin n => (cc 0 (j.val + 1) : Q (n + 1))) j).symm

theorem cc_eq_fi {n : ℕ} (j : Fin n) : (cc (j.val + 1) 0 : Q (n + 1)) = fi (Pi.single j 1) :=
  (cprod_single (fun j : Fin n => (cc (j.val + 1) 0 : Q (n + 1))) j).symm

/-- The set of fan-outs. -/
def foSet (n : ℕ) : Set (Q (n + 1)) := {x | ∃ c, x = fo c}

theorem foSet_mul {n : ℕ} : ∀ x ∈ foSet n, ∀ y ∈ foSet n, x * y ∈ foSet n := by
  rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩; exact ⟨c + c', fo_mul c c'⟩

/-- The set of fan-ins. -/
def fiSet (n : ℕ) : Set (Q (n + 1)) := {x | ∃ c, x = fi c}

theorem fiSet_mul {n : ℕ} : ∀ x ∈ fiSet n, ∀ y ∈ fiSet n, x * y ∈ fiSet n := by
  rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩; exact ⟨c + c', fi_mul c c'⟩

theorem cc_foSet {n : ℕ} {k : ℕ} (hk : k < n) : (cc 0 (k + 1) : Q (n + 1)) ∈ foSet n :=
  ⟨_, cc_eq_fo ⟨k, hk⟩⟩

theorem cc_fiSet {n : ℕ} {k : ℕ} (hk : k < n) : (cc (k + 1) 0 : Q (n + 1)) ∈ fiSet n :=
  ⟨_, cc_eq_fi ⟨k, hk⟩⟩

theorem conj_qSW1 {n : ℕ} {i : ℕ} (hi : i + 2 < n + 1) {a b : ℕ} (hab : a ≠ b) (ha : a < n + 1)
    (hb : b < n + 1) :
    (qSW (i + 1) : Q (n + 1)) * cc a b * qSW (i + 1) =
      cc (if a = i + 1 then i + 2 else if a = i + 2 then i + 1 else a)
        (if b = i + 1 then i + 2 else if b = i + 2 then i + 1 else b) := by
  have e := cc_conj (n := n + 1) [i + 1] hab (a' := if a = i + 1 then i + 2 else if a = i + 2 then i + 1 else a)
    (b' := if b = i + 1 then i + 2 else if b = i + 2 then i + 1 else b)
    (by split_ifs <;> omega) ha hb (by split_ifs <;> omega) (by split_ifs <;> omega)
    (fun s => by rw [swp_singleton, paQ_qSW]; simp only; rw [bit_comp_swq _ hi]; split_ifs <;> first | rfl | (congr 1; omega))
    (fun s => by rw [swp_singleton, paQ_qSW]; simp only; rw [bit_comp_swq _ hi]; split_ifs <;> first | rfl | (congr 1; omega))
  rw [swp_singleton, qSW_inv] at e
  exact e

/-- A fan-out conjugated by a linear generator one wire up is a fan-out. -/
theorem fo_conj_gen {n : ℕ} {g : Q n} (hg : g ∈ linGens n) (c : State 2 n) :
    sh g * fo c * sh g ∈ foSet n := by
  have hconj : sh g * fo c * sh g = cprod (fun j : Fin n => sh g * cc 0 (j.val + 1) * sh g) c := by
    have := map_cprod (conjH (sh g)) (fun j : Fin n => (cc 0 (j.val + 1) : Q (n + 1))) c
    simp only [conjH_apply] at this
    have hinv : (sh g)⁻¹ = sh g := by rw [← map_inv, linGens_inv hg]
    rw [hinv] at this; exact this
  rw [hconj]
  refine cprod_mem (S := foSet n) ⟨0, fo_zero.symm⟩ foSet_mul (fun j => ?_) c
  obtain ⟨i, rfl | rfl⟩ := hg
  · rw [sh_qCX]
    by_cases hi : i + 2 < n + 1
    · rw [qCX_eq_cc hi]
      by_cases h2 : j.val + 1 = i + 2
      · rw [h2, cc_s3' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact foSet_mul _ (cc_foSet (by omega)) _ (cc_foSet (k := i) (by omega))
      · have hc : Commute (cc (i + 2) (i + 1) : Q (n + 1)) (cc 0 (j.val + 1)) := by
          by_cases h1 : j.val + 1 = i + 1
          · rw [h1]
            exact (cc_comm_tgt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
          · exact cc_comm_disj (by omega) (by omega) (by omega) (Ne.symm h2) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega)
        rw [hc.eq, mul_assoc, cc_sq, mul_one]
        exact cc_foSet j.isLt
    · rw [qCX_out (by omega), one_mul, mul_one]; exact cc_foSet j.isLt
  · rw [sh_qSW]
    by_cases hi : i + 2 < n + 1
    · rw [conj_qSW1 hi (by omega) (by omega) (by omega)]
      simp only [show (0 : ℕ) ≠ i + 1 by omega, show (0 : ℕ) ≠ i + 2 by omega, if_false]
      split_ifs with h1 h2
      · exact cc_foSet (k := i + 1) (by omega)
      · exact cc_foSet (k := i) (by omega)
      · exact cc_foSet j.isLt
    · rw [qSW_out (by omega), one_mul, mul_one]; exact cc_foSet j.isLt

/-- A fan-in conjugated by a linear generator one wire up is a fan-in. -/
theorem fi_conj_gen {n : ℕ} {g : Q n} (hg : g ∈ linGens n) (c : State 2 n) :
    sh g * fi c * sh g ∈ fiSet n := by
  have hconj : sh g * fi c * sh g = cprod (fun j : Fin n => sh g * cc (j.val + 1) 0 * sh g) c := by
    have := map_cprod (conjH (sh g)) (fun j : Fin n => (cc (j.val + 1) 0 : Q (n + 1))) c
    simp only [conjH_apply] at this
    have hinv : (sh g)⁻¹ = sh g := by rw [← map_inv, linGens_inv hg]
    rw [hinv] at this; exact this
  rw [hconj]
  refine cprod_mem (S := fiSet n) ⟨0, fi_zero.symm⟩ fiSet_mul (fun j => ?_) c
  obtain ⟨i, rfl | rfl⟩ := hg
  · rw [sh_qCX]
    by_cases hi : i + 2 < n + 1
    · rw [qCX_eq_cc hi]
      by_cases h1 : j.val + 1 = i + 1
      · rw [h1, cc_s3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact fiSet_mul _ (cc_fiSet (k := i) (by omega)) _ (cc_fiSet (k := i + 1) (by omega))
      · have hc : Commute (cc (i + 2) (i + 1) : Q (n + 1)) (cc (j.val + 1) 0) := by
          by_cases h2 : j.val + 1 = i + 2
          · rw [h2]
            exact cc_comm_ctrl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          · exact cc_comm_disj (by omega) (by omega) (Ne.symm h2) (by omega) (Ne.symm h1)
              (by omega) (by omega) (by omega) (by omega) (by omega)
        rw [hc.eq, mul_assoc, cc_sq, mul_one]
        exact cc_fiSet j.isLt
    · rw [qCX_out (by omega), one_mul, mul_one]; exact cc_fiSet j.isLt
  · rw [sh_qSW]
    by_cases hi : i + 2 < n + 1
    · rw [conj_qSW1 hi (by omega) (by omega) (by omega)]
      simp only [show (0 : ℕ) ≠ i + 1 by omega, show (0 : ℕ) ≠ i + 2 by omega, if_false]
      split_ifs with h1 h2
      · exact cc_fiSet (k := i + 1) (by omega)
      · exact cc_fiSet (k := i) (by omega)
      · exact cc_fiSet j.isLt
    · rw [qSW_out (by omega), one_mul, mul_one]; exact cc_fiSet j.isLt

theorem fo_push {n : ℕ} {h : Q n} (hh : h ∈ Lin n) : ∀ c : State 2 n, ∃ c', fo c * sh h = sh h * fo c' := by
  induction hh using Subgroup.closure_induction'' with
  | mem g hg =>
    intro c
    obtain ⟨c', e⟩ := fo_conj_gen hg c
    refine ⟨c', ?_⟩
    rw [← e, ← mul_assoc, ← mul_assoc, ← map_mul, linGens_sq hg, map_one, one_mul]
  | inv_mem g hg =>
    intro c
    obtain ⟨c', e⟩ := fo_conj_gen hg c
    refine ⟨c', ?_⟩
    rw [linGens_inv hg, ← e, ← mul_assoc, ← mul_assoc, ← map_mul, linGens_sq hg, map_one, one_mul]
  | one => intro c; exact ⟨c, by simp⟩
  | mul x y _ _ hx hy =>
    intro c
    obtain ⟨c1, e1⟩ := hx c
    obtain ⟨c2, e2⟩ := hy c1
    exact ⟨c2, by rw [map_mul, ← mul_assoc, e1, mul_assoc, e2, mul_assoc]⟩

theorem fi_push_gen {n : ℕ} {g : Q n} (hg : g ∈ linGens n) (c : State 2 n) :
    ∃ c', fi c * sh g = sh g * fi c' := by
  obtain ⟨c', e⟩ := fi_conj_gen hg c
  refine ⟨c', ?_⟩
  rw [← e, ← mul_assoc, ← mul_assoc, ← map_mul, linGens_sq hg, map_one, one_mul]

/-! ### Fans on the lower wires -/

/-- The fan-in into wire `0` from the wires `j + 2`. -/
noncomputable def fi2 {n : ℕ} (c : State 2 n) : Q (n + 2) := cprod (fun j : Fin n => cc (j.val + 2) 0) c

theorem fi_cons {n : ℕ} (a : Fin 2) (c : State 2 n) :
    (fi (Fin.cons a c : State 2 (n + 1)) : Q (n + 2)) = cc 1 0 ^ a.val * fi2 c := by
  rw [fi, cprod_succ]; rfl

theorem sh_fi {n : ℕ} (c : State 2 n) :
    sh (fi c : Q (n + 1)) = cprod (fun j : Fin n => cc (j.val + 2) 1) c := by
  rw [fi, map_cprod]
  congr 1; funext j; exact sh_cc (by omega) (by omega) (by omega)

theorem sh_fo {n : ℕ} (c : State 2 n) :
    sh (fo c : Q (n + 1)) = cprod (fun j : Fin n => cc 1 (j.val + 2)) c := by
  rw [fo, map_cprod]
  congr 1; funext j; exact sh_cc (by omega) (by omega) (by omega)

/-- The transposition of `0` and `1` on wire indices. -/
def sw01 (a : ℕ) : ℕ := if a = 0 then 1 else if a = 1 then 0 else a

theorem sw01_zero : sw01 0 = 1 := rfl

theorem sw01_one : sw01 1 = 0 := rfl

theorem sw01_ge {a : ℕ} (h : 2 ≤ a) : sw01 a = a := by
  unfold sw01; rw [if_neg (by omega), if_neg (by omega)]

theorem sw01_lt {n a : ℕ} (h : a < n + 2) : sw01 a < n + 2 := by
  unfold sw01; split_ifs <;> omega

theorem sw01_inj {a b : ℕ} (h : a ≠ b) : sw01 a ≠ sw01 b := by
  unfold sw01; split_ifs <;> omega

theorem bit_swq0 {n : ℕ} (s : State 2 (n + 2)) (a : ℕ) : bit (s ∘ swq 0) (sw01 a) = bit s a := by
  rw [bit_comp_swq _ (by omega)]
  rcases Nat.lt_or_ge a 2 with h | h
  · interval_cases a <;> rfl
  · rw [sw01_ge h, if_neg (by omega), if_neg (by omega)]

theorem qSW0_cc {n : ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a < n + 2) (hb : b < n + 2) :
    (qSW 0 : Q (n + 2)) * cc a b * qSW 0 = cc (sw01 a) (sw01 b) := by
  have e := cc_conj (n := n + 2) [0] hab (a' := sw01 a) (b' := sw01 b)
    (sw01_inj hab) ha hb (sw01_lt ha) (sw01_lt hb)
    (fun s => by rw [swp_singleton, paQ_qSW]; exact bit_swq0 s a)
    (fun s => by rw [swp_singleton, paQ_qSW]; exact bit_swq0 s b)
  rw [swp_singleton, qSW_inv] at e
  exact e

/-- `SW₀₁` carries the fan-in into wire `0` from the wires `≥ 2` to the
fan-in into wire `1`. -/
theorem qSW0_fi2 {n : ℕ} (c : State 2 n) :
    (qSW 0 : Q (n + 2)) * fi2 c * qSW 0 = sh (fi c) := by
  have := map_cprod (conjH (qSW 0 : Q (n + 2))) (fun j : Fin n => (cc (j.val + 2) 0 : Q (n + 2))) c
  simp only [conjH_apply, qSW_inv] at this
  rw [fi2, this, sh_fi]
  congr 1; funext j
  rw [qSW0_cc (by omega) (by omega) (by omega), sw01_ge (a := j.val + 2) (by omega)]
  rfl

/-- `SW₀₁` carries the fan-out from wire `1` to the wires `≥ 2` to the
fan-out from wire `0`. -/
theorem qSW0_sh_fo {n : ℕ} (c : State 2 n) :
    (qSW 0 : Q (n + 2)) * sh (fo c) * qSW 0 = fo (Fin.cons 0 c) := by
  have := map_cprod (conjH (qSW 0 : Q (n + 2))) (fun j : Fin n => (cc 1 (j.val + 2) : Q (n + 2))) c
  simp only [conjH_apply, qSW_inv] at this
  rw [sh_fo, this, fo, cprod_succ]
  simp only [Fin.cons_zero, Fin.val_zero, pow_zero, one_mul, Fin.cons_succ, Fin.val_succ]
  congr 1; funext j
  rw [qSW0_cc (by omega) (by omega) (by omega), sw01_ge (a := j.val + 2) (by omega)]
  rfl

theorem fi1_comm {n : ℕ} (i j : Fin n) :
    Commute (cc (i.val + 2) 1 : Q (n + 2)) (cc (j.val + 2) 1) := by
  by_cases h : i = j
  · rw [h]
  · exact cc_comm_tgt (by simp [Fin.ext_iff] at h; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)

/-- The fan-in into wire `1`, conjugating `CNOT₁₀`. -/
theorem fi1_conj {n : ℕ} (c : State 2 n) :
    sh (fi c) * cc 1 0 * sh (fi c) = (cc 1 0 * fi2 c : Q (n + 2)) := by
  rw [sh_fi, fi2]
  refine cprod_conj_affine fi1_comm (fun _ => cc_sq _ _) (fun j => ?_) (fun i j => ?_) c
  · exact cc_s3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · by_cases h : i = j
    · rw [h]
      exact cc_comm_ctrl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact cc_comm_disj (by omega) (by omega) (by simp [Fin.ext_iff] at h; omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem cc01_comm_fi1 {n : ℕ} (c : State 2 n) : Commute (cc 0 1 : Q (n + 2)) (sh (fi c)) := by
  rw [sh_fi]
  exact cprod_comm (fun j =>
    (cc_comm_tgt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm) c

theorem fi_sq {n : ℕ} (c : State 2 n) : (fi c : Q (n + 1)) * fi c = 1 :=
  cprod_sq fi_comm (fun _ => cc_sq _ _) c

theorem qSW0_cc10 {n : ℕ} : (qSW 0 : Q (n + 2)) * cc 1 0 = cc 0 1 * qSW 0 := by
  have e : (qSW 0 : Q (n + 2)) * cc 1 0 * qSW 0 = cc 0 1 :=
    qSW0_cc (n := n) (a := 1) (b := 0) (by omega) (by omega) (by omega)
  rw [← e, mul_assoc, qSW_sq, mul_one]

theorem cc10_qSW0 {n : ℕ} : (cc 1 0 : Q (n + 2)) * qSW 0 = cc 0 1 * cc 1 0 := by
  rw [qSW_eq_cc (by omega)]
  simp only [zero_add, ← mul_assoc, cc_sq, one_mul]

/-! ### Closure under the generators -/

theorem linGens_cases {n : ℕ} {g : Q (n + 1)} (hg : g ∈ linGens (n + 1)) :
    g = qCX 0 ∨ g = qSW 0 ∨ ∃ g' ∈ linGens n, g = sh g' := by
  obtain ⟨i, rfl | rfl⟩ := hg
  · rcases i with _ | i
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨qCX i, ⟨i, Or.inl rfl⟩, rfl⟩)
  · rcases i with _ | i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨qSW i, ⟨i, Or.inr rfl⟩, rfl⟩)

theorem fi2_eq {n : ℕ} (c : State 2 n) : (fi (Fin.cons 0 c) : Q (n + 2)) = fi2 c := by
  rw [fi_cons]; simp

/-- Multiplying a row representative on the right by a generator. -/
theorem R_mul_gen : ∀ (n : ℕ) (r : State 2 (n + 1)), r ≠ 0 → ∀ g ∈ linGens (n + 1),
    ∃ h ∈ Lin n, ∃ d : State 2 n, ∃ r' : State 2 (n + 1), r' ≠ 0 ∧
      R r * g = sh h * fo d * R r'
  | n, r, hr, g, hg => by
    rcases linGens_cases hg with rfl | rfl | ⟨g', hg', rfl⟩
    · -- `CNOT₁₀`
      cases n with
      | zero => exact ⟨1, (Lin 0).one_mem, 0, r, hr, by rw [qCX_out (by omega), fo_zero]; simp⟩
      | succ n =>
        obtain ⟨a, t, rfl⟩ : ∃ a t, r = Fin.cons a t :=
          ⟨r 0, Fin.tail r, (Fin.cons_self_tail r).symm⟩
        rcases fin2_cases a with rfl | rfl
        · obtain ⟨b, rest, rfl⟩ : ∃ b rest, t = Fin.cons b rest :=
            ⟨t 0, Fin.tail t, (Fin.cons_self_tail t).symm⟩
          rcases fin2_cases b with rfl | rfl
          · -- `r = (0, 0, rest)`
            have hrest : rest ≠ 0 := by
              intro h; apply hr; subst h; funext j
              refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => rfl) j) j
            cases n with
            | zero => exact absurd (funext fun j => j.elim0) hrest
            | succ n =>
              refine ⟨qCX 0, qCX_mem_Lin 0, 0, _, hr, ?_⟩
              rw [R_cons_zero, R_cons_zero, fo_zero, mul_one, map_mul, sh_qSW, sh_qCX]
              rw [mul_assoc, mul_assoc, ← qCX0_comm_sh2, ← mul_assoc, ← mul_assoc, qSW_qCX0]
              simp only [mul_assoc]
          · -- `r = (0, 1, rest)`
            refine ⟨fi rest, fi_mem_Lin rest, Pi.single 0 1, _, hr, ?_⟩
            have hf : (fo (Pi.single (0 : Fin (n + 1)) 1) : Q (n + 2)) = cc 0 1 := (cc_eq_fo 0).symm
            rw [R_cons_zero, R_cons_one, hf, ← cc_one_zero]
            have hD := fi1_conj (n := n) rest
            have hN : sh (fi rest) * cc 1 0 = (cc 1 0 * fi2 rest : Q (n + 2)) * sh (fi rest) := by
              rw [← hD, mul_assoc, ← map_mul, fi_sq, map_one, mul_one]
            have hC : (qSW 0 : Q (n + 2)) * fi2 rest = sh (fi rest) * qSW 0 := by
              rw [← qSW0_fi2, mul_assoc, qSW_sq, mul_one]
            calc qSW 0 * sh (fi rest) * cc 1 0
                = qSW 0 * cc 1 0 * fi2 rest * sh (fi rest) := by
                  rw [mul_assoc, hN]; simp only [mul_assoc]
              _ = cc 0 1 * (qSW 0 * fi2 rest) * sh (fi rest) := by
                  rw [qSW0_cc10]; simp only [mul_assoc]
              _ = cc 0 1 * sh (fi rest) * (qSW 0 * sh (fi rest)) := by
                  rw [hC]; simp only [mul_assoc]
              _ = sh (fi rest) * cc 0 1 * (qSW 0 * sh (fi rest)) := by
                  rw [(cc01_comm_fi1 rest).eq]
        · -- `r = (1, t)`
          refine ⟨1, (Lin _).one_mem, 0, Fin.cons 1 (t + Pi.single 0 1), cons_ne_zero_one _, ?_⟩
          rw [R_cons_one, R_cons_one, map_one, fo_zero, one_mul, one_mul, ← cc_one_zero,
            show (cc 1 0 : Q (n + 2)) = cc ((0 : Fin (n + 1)).val + 1) 0 from rfl, cc_eq_fi,
            fi_mul]
    · -- `SWAP₀₁`
      cases n with
      | zero => exact ⟨1, (Lin 0).one_mem, 0, r, hr, by rw [qSW_out (by omega), fo_zero]; simp⟩
      | succ n =>
        obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, r = Fin.cons a (Fin.cons b rest) :=
          ⟨r 0, r 1, Fin.tail (Fin.tail r), by
            conv_lhs => rw [← Fin.cons_self_tail r, ← Fin.cons_self_tail (Fin.tail r)]
            rfl⟩
        have hC : (qSW 0 : Q (n + 2)) * fi2 rest = sh (fi rest) * qSW 0 := by
          rw [← qSW0_fi2, mul_assoc, qSW_sq, mul_one]
        have hC' : fi2 rest * qSW 0 = (qSW 0 : Q (n + 2)) * sh (fi rest) := by
          rw [← qSW0_fi2, ← mul_assoc, ← mul_assoc, qSW_sq, one_mul]
        rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl
        · -- `(0, 0, rest)`
          have hrest : rest ≠ 0 := by
            intro h; apply hr; subst h; funext j
            refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => rfl) j) j
          cases n with
          | zero => exact absurd (funext fun j => j.elim0) hrest
          | succ n =>
            refine ⟨qSW 0, qSW_mem_Lin 0, 0, _, hr, ?_⟩
            rw [R_cons_zero, R_cons_zero, fo_zero, mul_one, map_mul, sh_qSW]
            rw [mul_assoc, mul_assoc, ← qSW0_comm_sh2, ← mul_assoc, ← mul_assoc,
              qSW_braid 0 (by omega)]
            simp only [mul_assoc]
        · -- `(0, 1, rest)`
          refine ⟨1, (Lin _).one_mem, 0, Fin.cons 1 (Fin.cons 0 rest), cons_ne_zero_one _, ?_⟩
          rw [R_cons_zero, R_cons_one, R_cons_one, map_one, fo_zero, one_mul, one_mul, fi2_eq,
            ← qSW0_fi2, ← mul_assoc, ← mul_assoc, qSW_sq, one_mul, mul_assoc, qSW_sq, mul_one]
        · -- `(1, 0, rest)`
          refine ⟨1, (Lin _).one_mem, 0, Fin.cons 0 (Fin.cons 1 rest),
            cons_ne_zero (cons_ne_zero_one rest) 0, ?_⟩
          rw [R_cons_one, R_cons_zero, R_cons_one, map_one, fo_zero, one_mul, one_mul, fi2_eq, hC']
        · -- `(1, 1, rest)`
          refine ⟨fi rest, fi_mem_Lin rest, Pi.single 0 1, _, hr, ?_⟩
          have hf : (fo (Pi.single (0 : Fin (n + 1)) 1) : Q (n + 2)) = cc 0 1 := (cc_eq_fo 0).symm
          rw [R_cons_one, fi_cons, hf]
          simp only [Fin.val_one, pow_one]
          have hD := fi1_conj (n := n) rest
          have hC2 : fi2 rest * qSW 0 = (qSW 0 : Q (n + 2)) * sh (fi rest) := by
            rw [← qSW0_fi2, ← mul_assoc, ← mul_assoc, qSW_sq, one_mul]
          have hss : sh (fi rest) * sh (fi rest) = (1 : Q (n + 2)) := by
            rw [← map_mul, fi_sq, map_one]
          calc cc 1 0 * fi2 rest * qSW 0
              = cc 1 0 * qSW 0 * sh (fi rest) := by rw [mul_assoc, hC2, ← mul_assoc]
            _ = cc 0 1 * (sh (fi rest) * (sh (fi rest) * cc 1 0 * sh (fi rest))) := by
                rw [cc10_qSW0, show sh (fi rest) * (sh (fi rest) * cc 1 0 * sh (fi rest)) =
                  (sh (fi rest) * sh (fi rest)) * cc 1 0 * sh (fi rest) by group, hss, one_mul,
                  mul_assoc]
            _ = sh (fi rest) * cc 0 1 * (cc 1 0 * fi2 rest) := by
                rw [hD, ← mul_assoc, (cc01_comm_fi1 rest).eq]
    · -- a generator one wire up
      obtain ⟨a, t, rfl⟩ : ∃ a t, r = Fin.cons a t := ⟨r 0, Fin.tail r, (Fin.cons_self_tail r).symm⟩
      rcases fin2_cases a with rfl | rfl
      · cases n with
        | zero => exact absurd (funext fun j => by rw [Fin.fin_one_eq_zero j]; rfl) hr
        | succ n =>
          have ht : t ≠ 0 := by have := tail_ne_zero hr (by simp); simpa using this
          obtain ⟨h', hh', d', r'', hr'', e⟩ := R_mul_gen n t ht g' hg'
          refine ⟨sh h', sh_mem_Lin hh', Fin.cons 0 d', Fin.cons 0 r'', cons_ne_zero hr'' 0, ?_⟩
          rw [R_cons_zero, R_cons_zero, mul_assoc, ← map_mul, e, map_mul, map_mul, ← qSW0_sh_fo]
          simp only [mul_assoc, qSW_sq_left]
          rw [← mul_assoc, qSW0_comm_sh2, mul_assoc]
      · obtain ⟨t', e⟩ := fi_push_gen hg' t
        refine ⟨g', Subgroup.subset_closure hg', 0, Fin.cons 1 t', cons_ne_zero_one _, ?_⟩
        rw [R_cons_one, R_cons_one, e, fo_zero, mul_one]

/-! ### The normal form and its uniqueness -/

theorem nf_mul_gen {n : ℕ} {x : Q (n + 1)}
    (hx : ∃ h ∈ Lin n, ∃ c : State 2 n, ∃ r : State 2 (n + 1), r ≠ 0 ∧ x = sh h * fo c * R r)
    {g : Q (n + 1)} (hg : g ∈ linGens (n + 1)) :
    ∃ h ∈ Lin n, ∃ c : State 2 n, ∃ r : State 2 (n + 1), r ≠ 0 ∧ x * g = sh h * fo c * R r := by
  obtain ⟨h, hh, c, r, hr, rfl⟩ := hx
  obtain ⟨h1, hh1, d, r', hr', e⟩ := R_mul_gen n r hr g hg
  obtain ⟨c', e'⟩ := fo_push hh1 c
  refine ⟨h * h1, (Lin n).mul_mem hh hh1, c' + d, r', hr', ?_⟩
  rw [mul_assoc, e, ← fo_mul, map_mul]
  calc sh h * fo c * (sh h1 * fo d * R r') = sh h * (fo c * sh h1) * fo d * R r' := by
        simp only [mul_assoc]
    _ = _ := by rw [e']; simp only [mul_assoc]

/-- **Normal form of linear circuits**: `sh h * fo c * R r`. -/
theorem lin_nf {n : ℕ} {a : Q (n + 1)} (ha : a ∈ Lin (n + 1)) :
    ∃ h ∈ Lin n, ∃ c : State 2 n, ∃ r : State 2 (n + 1), r ≠ 0 ∧ a = sh h * fo c * R r := by
  induction ha using Subgroup.closure_induction_right with
  | one =>
    exact ⟨1, (Lin n).one_mem, 0, Fin.cons 1 0, cons_ne_zero_one 0, by
      rw [R_cons_one, fi_zero, fo_zero, map_one, one_mul, one_mul]⟩
  | mul_right x _ g hg ih => exact nf_mul_gen ih hg
  | mul_inv_cancel x _ g hg ih => rw [linGens_inv hg]; exact nf_mul_gen ih hg

theorem bit_sh_zero {n : ℕ} (h : Q n) (s : State 2 (n + 1)) :
    bit ((paQ (sh h)).f s) 0 = bit s 0 := by
  rw [paQ_sh_f, bit_cons_zero]; simp [bit]

theorem bit_fo_zero {n : ℕ} (c : State 2 n) (s : State 2 (n + 1)) :
    bit ((paQ (fo c)).f s) 0 = bit s 0 := by
  rw [paQ_fo]; simp [bit_add, bit_smul]

/-- The output on wire `0` of a normal form is `r · x`. -/
theorem bit_nf {n : ℕ} (h : Q n) (c : State 2 n) {r : State 2 (n + 1)} (hr : r ≠ 0)
    (s : State 2 (n + 1)) : bit ((paQ (sh h * fo c * R r)).f s) 0 = dot r s := by
  rw [map_mul, map_mul]
  show bit ((paQ (sh h)).f ((paQ (fo c)).f ((paQ (R r)).f s))) 0 = _
  rw [bit_sh_zero, bit_fo_zero, bit_R r hr]

theorem dot_single {n : ℕ} (r : State 2 n) (j : Fin n) : dot r (Pi.single j 1) = r j := by
  simp [dot, Pi.single_apply]

theorem paQ_f_injective {n : ℕ} (q : Q n) : Function.Injective (paQ q).f := fun s t h => by
  rw [← paQ_inv_f' q s, h, paQ_inv_f']

/-- On `0` wires there are no linear gates. -/
theorem Lin_zero : Lin 0 = ⊥ := by
  rw [Lin, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨i, rfl | rfl⟩
  · exact qCX_out (by omega)
  · exact qSW_out (by omega)

/-- Cancelling on the right in the semantics. -/
theorem paQ_cancel_right {n : ℕ} {a b c : Q n} (h : paQ (a * c) = paQ (b * c)) : paQ a = paQ b := by
  have := congrArg (· * paQ c⁻¹) h
  simp only [← map_mul, mul_assoc, mul_inv_cancel, mul_one] at this
  exact this

/-- **Completeness for linear circuits**: linear circuits with the same
pair (the same linear map) are equal in the theory. -/
theorem lin_complete : ∀ (n : ℕ) {a b : Q n}, a ∈ Lin n → b ∈ Lin n → paQ a = paQ b → a = b
  | 0, a, b, ha, hb, _ => by
    rw [Lin_zero, Subgroup.mem_bot] at ha hb; rw [ha, hb]
  | n + 1, a, b, ha, hb, hab => by
    obtain ⟨h, hh, c, r, hr, rfl⟩ := lin_nf ha
    obtain ⟨h', hh', c', r', hr', rfl⟩ := lin_nf hb
    -- the rows agree
    have hrr : r = r' := by
      funext j
      have := congrArg (fun p : PA (n + 1) => bit (p.f (Pi.single j 1)) 0) hab
      simp only at this
      rwa [bit_nf h c hr, bit_nf h' c' hr', dot_single, dot_single] at this
    subst hrr
    have e1 : paQ (sh h * fo c) = paQ (sh h' * fo c') := paQ_cancel_right hab
    -- the upper maps agree
    have hf : ∀ t : State 2 n, (paQ h).f t = (paQ h').f t := by
      intro t
      have := congrArg (fun p : PA (n + 1) => Fin.tail (p.f (Fin.cons 0 t))) e1
      simp only [map_mul, PA.mul_f, Function.comp_apply, paQ_fo, paQ_sh_f] at this
      simpa using this
    -- the fan-outs agree
    have hc : c = c' := by
      have := congrArg (fun p : PA (n + 1) => Fin.tail (p.f (Fin.cons 1 0))) e1
      simp only [map_mul, PA.mul_f, Function.comp_apply, paQ_fo, paQ_sh_f] at this
      simp [cons_add] at this
      rw [hf] at this
      exact paQ_f_injective h' this
    subst hc
    have hp : paQ h = paQ h' := by
      refine PA.ext' hf (fun s => ?_)
      rw [(lin_pa hh).1, (lin_pa hh').1]
    rw [lin_complete n hh hh' hp]

end QCert.CNOTDihedral
