/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: tools for the squares of the Main Lemma

For a state `s` with pivot `p` and a generator `x` acting on indices at most
`p`, the state `r = x s` has the same columns beyond `p`, and its pivot
column is `x` applied to that of `s` (`isPivot_sem`).  The letters `X` and
`i` keep the profile of every column (`prof_sem_X`, `prof_sem_i`), so a
path of such letters from `t = N s` stays below the level of `s`
(`allBelow_mon`).  The squares of the Main Lemma are then closed by
`step_sq` (one normal edge from `r`), `step_sq0` (no normal edge from `r`),
`step_disj` (the disjoint case) and `step_retro'` (the retrograde case).
-/
import QCert.BianSelingerUn.LevelBound
import QCert.BianSelingerUn.Derived

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-! ### Columns after a generator -/

theorem col_sem (x : Gen n) (s : St n) (q : Fin n) : col (sem n x * s) q = mat x *ᵥ col s q := by
  rw [col_mul, sm_sem]

theorem mat_mulVec_ev_of_lt (x : Gen n) {q : Fin n} (hq : ext x < (q : ℕ)) :
    mat x *ᵥ ev q = ev q := by
  cases x with
  | X a c h =>
    change (c : ℕ) < q at hq
    have hac : (a : ℕ) < c := h
    exact twoLevel_mulVec_of_zero h.ne _ (ev_apply_ne (fun e => by subst e; omega))
      (ev_apply_ne (fun e => by subst e; omega))
  | K a c h =>
    change (c : ℕ) < q at hq
    have hac : (a : ℕ) < c := h
    exact twoLevel_mulVec_of_zero h.ne _ (ev_apply_ne (fun e => by subst e; omega))
      (ev_apply_ne (fun e => by subst e; omega))
  | i a =>
    change (a : ℕ) < q at hq
    exact oneLevel_mulVec_of_zero _ _ (ev_apply_ne (fun e => by subst e; omega))

theorem isPivot_sem {s : St n} {p : Fin n} (hp : IsPivot s p) {x : Gen n} (hx : ext x ≤ (p : ℕ))
    (hne : mat x *ᵥ col s p ≠ ev p) : IsPivot (sem n x * s) p :=
  ⟨by rwa [col_sem], fun q hq => by
    rw [col_sem, hp.2 q hq, mat_mulVec_ev_of_lt x (by have : (p : ℕ) < q := hq; omega)]⟩

theorem HasNum.eq_of {u u' : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum u k w)
    (h' : HasNum u' k w) : u = u' :=
  funext fun j => mul_left_cancel₀ (pow_ne_zero k γ_ne_zero) ((h j).trans (h' j).symm)

theorem lde_ev (p : Fin n) : lde (ev p) = 0 := by
  have h : HasNum (ev p) 0 (fun a => if a = p then 1 else 0) := by
    intro a; by_cases ha : a = p <;> simp [ev, ha]
  exact lde_eq h (Or.inl rfl)

theorem ne_ev_of_odd {u : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum u k w)
    (hk : 0 < k) (hodd : ∃ j, GOdd (w j)) (p : Fin n) : u ≠ ev p := by
  rintro rfl
  have := lde_eq h (Or.inr hodd)
  rw [lde_ev] at this; omega

theorem lde_of_odd {u : Fin n → ℂ} {k : ℕ} {w : Fin n → GaussianInt} (h : HasNum u k w)
    (j : Fin n) (hj : GOdd (w j)) : lde u = k := lde_eq h (Or.inr ⟨j, hj⟩)

/-! ### Numerators after a generator -/

theorem hasNum_sem_i {s : St n} {q : Fin n} {k : ℕ} {w : Fin n → GaussianInt}
    (h : HasNum (col s q) k w) (a : Fin n) :
    HasNum (col (sem n (Gen.i a) * s) q) k (Function.update w a (iz * w a)) := by
  have := hasNum_oneLevel h a 1
  simp only [pow_one] at this
  rw [col_sem]; exact this

theorem hasNum_sem_X {s : St n} {q : Fin n} {k : ℕ} {w : Fin n → GaussianInt}
    (h : HasNum (col s q) k w) {a b : Fin n} (hab : a < b) :
    HasNum (col (sem n (Gen.X a b hab) * s) q) k
      (Function.update (Function.update w a (w b)) b (w a)) := by
  rw [col_sem]; exact hasNum_X h hab.ne

theorem hasNum_sem_K {s : St n} {q : Fin n} {k : ℕ} {w : Fin n → GaussianInt}
    (h : HasNum (col s q) k w) {a b : Fin n} (hab : a < b) :
    HasNum (col (sem n (Gen.K a b hab) * s) q) (k + 1)
      (Function.update (Function.update (fun c => γz * w c) a (w a + w b)) b (w a - w b)) := by
  rw [col_sem]; exact hasNum_K h hab.ne

/-! ### Profiles under `X` and `i` -/

theorem twoLevel_X_mulVec {a b : Fin n} (hab : a ≠ b) (v : Fin n → ℂ) :
    twoLevel a b Xmat *ᵥ v = fun j => v (Equiv.swap a b j) := by
  rw [twoLevel_mulVec hab]
  funext j
  simp only [Function.update_apply, Xmat]
  by_cases hjb : j = b
  · subst hjb; simp
  by_cases hja : j = a
  · subst hja; simp [hjb]
  · simp [hjb, hja, Equiv.swap_apply_of_ne_of_ne hja hjb]

theorem prof_sem_X (s : St n) (q : Fin n) {a b : Fin n} (hab : a < b) :
    prof (col (sem n (Gen.X a b hab) * s) q) = prof (col s q) := by
  rw [col_sem]
  simp only [mat]
  rw [twoLevel_X_mulVec hab.ne]
  have := prof_perm (σ := Equiv.swap a b) (hasNum_exists s q)
  simpa using this

theorem prof_sem_i (s : St n) (q a : Fin n) :
    prof (col (sem n (Gen.i a) * s) q) = prof (col s q) := by
  have hw := num_spec (hasNum_exists s q)
  have hw' := hasNum_sem_i hw a
  have hl : lde (col (sem n (Gen.i a) * s) q) = lde (col s q) := by
    apply lde_eq hw'
    rcases Nat.eq_zero_or_pos (lde (col s q)) with h0 | hpos
    · exact Or.inl h0
    · obtain ⟨j, hj⟩ := exists_odd hw hpos
      refine Or.inr ⟨j, ?_⟩
      by_cases hja : j = a
      · subst hja; rw [Function.update_self, GOdd_iz_mul]; exact hj
      · rw [Function.update_of_ne hja]; exact hj
  rw [prof_eq hw' hl, prof_eq hw rfl]
  congr 2
  congr 1
  ext c
  simp only [mem_oddSet]
  by_cases hca : c = a
  · subst hca; rw [Function.update_self, GOdd_iz_mul]
  · rw [Function.update_of_ne hca]

/-! ### Paths of `X` and `i` letters -/

/-- A letter `X_[a,b]` or `i_[a]` on indices at most `p`. -/
def MonLetter (p : Fin n) : Gen n → Prop
  | .X _ b _ => b ≤ p
  | .K _ _ _ => False
  | .i a => a ≤ p

/-- The letter acts on the index `p`. -/
def Touches (p : Fin n) : Gen n → Prop
  | .X a b _ => a = p ∨ b = p
  | .K a b _ => a = p ∨ b = p
  | .i a => a = p

theorem mat_mulVec_ev_of_not_touch (x : Gen n) {p : Fin n} (h : ¬ Touches p x) :
    mat x *ᵥ ev p = ev p := by
  cases x with
  | X a b hab =>
    simp only [Touches, not_or] at h
    exact twoLevel_mulVec_of_zero hab.ne _ (ev_apply_ne h.1) (ev_apply_ne h.2)
  | K a b hab =>
    simp only [Touches, not_or] at h
    exact twoLevel_mulVec_of_zero hab.ne _ (ev_apply_ne h.1) (ev_apply_ne h.2)
  | i a => exact oneLevel_mulVec_of_zero _ _ (ev_apply_ne h)

theorem MonLetter.ext_le {p : Fin n} {x : Gen n} (h : MonLetter p x) : ext x ≤ (p : ℕ) := by
  cases x with
  | X a b hab => exact h
  | K a b hab => exact h.elim
  | i a => exact h

theorem mon_cols {p : Fin n} {t : St n} (htc : ∀ q, p < q → col t q = ev q) :
    ∀ (w : Word (Gen n)), (∀ x ∈ FreeMonoid.toList w, MonLetter p x) →
      ∀ q, p < q → col (⟪w⟫ * t) q = ev q := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => intro _ q hq; simpa using htc q hq
  | mul_of x w ih =>
    intro hw q hq
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc, col_sem,
      ih (fun y hy => hw y (by simp [hy])) q hq,
      mat_mulVec_ev_of_lt x (lt_of_le_of_lt (hw x (by simp)).ext_le hq)]

theorem mon_prof {t : St n} (q : Fin n) :
    ∀ (w : Word (Gen n)), (∀ x ∈ FreeMonoid.toList w, ∀ a b h, x ≠ Gen.K a b h) →
      prof (col (⟪w⟫ * t) q) = prof (col t q) := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => intro _; simp
  | mul_of x w ih =>
    intro hw
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc]
    have h2 := ih (fun y hy => hw y (by simp [hy]))
    cases x with
    | X a b hab => rw [prof_sem_X, h2]
    | K a b hab => exact absurd rfl (hw _ (by simp) a b hab)
    | i a => rw [prof_sem_i, h2]

theorem avoid_col {p : Fin n} {t : St n} (htp : col t p = ev p) :
    ∀ (w : Word (Gen n)), (∀ x ∈ FreeMonoid.toList w, ¬ Touches p x) → col (⟪w⟫ * t) p = ev p := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => intro _; simpa using htp
  | mul_of x w ih =>
    intro hw
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc, col_sem,
      ih (fun y hy => hw y (by simp [hy])), mat_mulVec_ev_of_not_touch x (hw x (by simp))]

/-- A path of letters `X`, `i` on indices at most the pivot `p` of `s`, from
a state `t` below `s` that agrees with the identity beyond `p`, stays below
`s` — if the letters avoid `p` or the pivot column of `s` has a positive
exponent. -/
theorem allBelow_mon {s t : St n} {p : Fin n} (hs : IsPivot s p) (ht : level t < level s)
    (htc : ∀ q, p < q → col t q = ev q) {w : Word (Gen n)}
    (hw : ∀ x ∈ FreeMonoid.toList w, MonLetter p x)
    (hk : 0 < lde (col s p) ∨ ∀ x ∈ FreeMonoid.toList w, ¬ Touches p x) :
    AllBelow (level s) t w := by
  intro u v huv
  have hv : ∀ x ∈ FreeMonoid.toList v, MonLetter p x := fun x hx =>
    hw x (by rw [huv, FreeMonoid.toList_mul]; exact List.mem_append_right _ hx)
  have hvK : ∀ x ∈ FreeMonoid.toList v, ∀ a b h, x ≠ Gen.K a b h := by
    intro x hx a b h e; subst e; exact hv _ hx
  apply level_lt_of_cols hs (mon_cols htc v hv)
  by_cases htp : col t p = ev p
  · rcases hk with hk | hk
    · right
      rw [mon_prof p v hvK, htp, prof_ev]
      rw [prof, Prod.Lex.toLex_lt_toLex]; left; exact hk
    · left
      have hvt : ∀ x ∈ FreeMonoid.toList v, ¬ Touches p x := fun x hx =>
        hk x (by rw [huv, FreeMonoid.toList_mul]; exact List.mem_append_right _ hx)
      exact avoid_col htp v hvt
  · right
    rw [mon_prof p v hvK]
    have hpt : IsPivot t p := ⟨htp, htc⟩
    rw [level_eq hpt, level_eq hs, Prod.Lex.toLex_lt_toLex] at ht
    rcases ht with h | ⟨-, h⟩
    · exact absurd h (lt_irrefl _)
    · exact h

theorem allBelow_one {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} (h : level t < L) : AllBelow L t 1 := by
  intro u v huv
  have hv : v = 1 := by
    have := congrArg FreeMonoid.toList huv
    rw [FreeMonoid.toList_mul, FreeMonoid.toList_one] at this
    exact FreeMonoid.toList.injective (List.append_eq_nil_iff.1 this.symm).2
  rw [hv, map_one, one_mul]; exact h

theorem allBelow_single {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} {x : Gen n} (h1 : level t < L)
    (h2 : level (sem n x * t) < L) : AllBelow L t (FreeMonoid.of x) := by
  intro u v huv
  rcases of_eq_mul_iff.1 huv with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rwa [FreeMonoid.lift_eval_of]
  · rwa [map_one, one_mul]

/-! ### Closing squares -/

theorem sem_eq_of_cl {N' G' N : Word (Gen n)} {x : Gen n}
    (h : cl (N' * FreeMonoid.of x) = cl (G' * N)) : ⟪N'⟫ * sem n x = ⟪G'⟫ * ⟪N⟫ := by
  have := lift_eq_of_cl h
  rwa [map_mul, map_mul, FreeMonoid.lift_eval_of] at this

/-- A square of the Main Lemma whose right side is the normal edge of `r = x s`. -/
theorem step_sq {s : St n} (hs : s ≠ 1) {x : Gen n} (hr : sem n x * s ≠ 1) (G' : Word (Gen n))
    (hrel : cl (syl (sem n x * s) * FreeMonoid.of x) = cl (G' * syl s))
    (hG : AllBelow (level s) (⟪syl s⟫ * s) G')
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s x := by
  refine step_of_square hs (syl (sem n x * s)) G' (⟪syl (sem n x * s)⟫ * (sem n x * s))
    (nw_eq_of_syl hr rfl) ?_ hG (derivable_iff.2 hrel) hstep
  rw [← mul_assoc, ← sem_eq_of_cl hrel, mul_assoc]

/-- A square of the Main Lemma with no normal edge on the right (`q = r`). -/
theorem step_sq0 {s : St n} (hs : s ≠ 1) {x : Gen n} (G' : Word (Gen n))
    (hrel : cl (FreeMonoid.of x) = cl (G' * syl s))
    (hG : AllBelow (level s) (⟪syl s⟫ * s) G')
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s x := by
  refine step_of_square hs 1 G' (sem n x * s) (mul_one _).symm ?_ hG
    (derivable_iff.2 (by simpa using hrel)) hstep
  have := sem_eq_of_cl (N' := 1) (by simpa using hrel)
  rw [map_one, one_mul] at this
  rw [← mul_assoc, ← this]

/-- The disjoint case: `r` has the syllable of `s`, which commutes with `x`. -/
theorem step_disj {s : St n} (hs : s ≠ 1) {x : Gen n} (hr : sem n x * s ≠ 1)
    (hsyl : syl (sem n x * s) = syl s) (hlev : level (sem n x * s) ≤ level s)
    (hrel : cl (syl s * FreeMonoid.of x) = cl (FreeMonoid.of x * syl s))
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s x := by
  refine step_sq hs hr (FreeMonoid.of x) (by rw [hsyl]; exact hrel) ?_ hstep
  apply allBelow_single (level_syl_lt hs)
  have := sem_eq_of_cl (N' := syl s) (G' := FreeMonoid.of x) (N := syl s) hrel
  rw [FreeMonoid.lift_eval_of] at this
  rw [← mul_assoc, ← this, mul_assoc, ← hsyl]
  exact lt_of_lt_of_le (level_syl_lt hr) hlev

/-- A retrograde edge: the normal edge of `r = x s` is a word inverse to `x`. -/
theorem step_retro' {s : St n} {x : Gen n} (hr : sem n x * s ≠ 1) {u : Word (Gen n)}
    (hsyl : syl (sem n x * s) = u) (hrel : cl (u * FreeMonoid.of x) = 1) : Step s x := by
  refine step_of_retro hr hsyl ?_ (derivable_iff.2 (by rw [hrel, map_one]))
  have := sem_eq_of_cl (N' := u) (G' := 1) (N := 1) (by rw [hrel]; simp)
  rw [map_one, one_mul] at this
  rw [← mul_assoc, this, one_mul]

end

end QCert.BianSelingerUn
