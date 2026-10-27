/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the level part of Lemma 30

Lemma 30 (c): for a simple edge `s → r` and the corresponding sequence of
basic edges `s → s₁ → ⋯ → r`, `level(sᵢ) ≤ max(level s, level r)`.  The
intermediate states of the basic word of a generator `y` of extent `e`
(Definition 29) are `P s` or `P (y s)` for permutation matrices `P` fixing
the indices above `e` (`SufOK`): all letters but one are `X`'s of extent at
most `e`, as in the proof.  Such a `P` does not raise the level of a state
whose pivot is at least `e` (`level_perm_le`), and turns a state equal to
the identity from `e` on into one of level at most `(e + 1, 0, 0)`
(`level_perm_low`), which is below the level of any state with pivot at
least `e`; and `y` moves `e_e`, so one of `s`, `y s` has pivot at least `e`.
Hence `Step` along simple edges follows from `Step` along basic ones
(`lift_basic'`).
-/
import QCert.Greylyn.Decomp

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-! ### Permutation states -/

/-- `P` is a permutation matrix fixing the indices above `e`. -/
def IsPerm (P : St n) (e : ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), (∀ q : Fin n, e < (q : ℕ) → σ q = q) ∧ ∀ q, col P q = ev (σ q)

theorem mulVec_ev (s : St n) (q : Fin n) : sm s *ᵥ ev q = col s q := by
  funext j; simp [mulVec, dotProduct, ev, col]

theorem IsPerm.one (e : ℕ) : IsPerm (1 : St n) e :=
  ⟨1, fun _ _ => rfl, fun q => col_one q⟩

theorem IsPerm.mul {P Q : St n} {e : ℕ} (hP : IsPerm P e) (hQ : IsPerm Q e) :
    IsPerm (P * Q) e := by
  obtain ⟨σ, hσ, hP⟩ := hP
  obtain ⟨τ, hτ, hQ⟩ := hQ
  refine ⟨τ.trans σ, fun q hq => ?_, fun q => ?_⟩
  · simp [hτ q hq, hσ q hq]
  · rw [col_mul, hQ, mulVec_ev, hP]; rfl

theorem IsPerm.mono {P : St n} {e e' : ℕ} (h : IsPerm P e) (he : e ≤ e') : IsPerm P e' := by
  obtain ⟨σ, hσ, hP⟩ := h
  exact ⟨σ, fun q hq => hσ q (by omega), hP⟩

theorem perm_mulVec {P : St n} {σ : Equiv.Perm (Fin n)} (hP : ∀ q, col P q = ev (σ q))
    (v : Fin n → ℂ) : sm P *ᵥ v = fun j => v (σ.symm j) := by
  funext j
  simp only [mulVec, dotProduct]
  have hent : ∀ a, sm P j a = if j = σ a then 1 else 0 := by
    intro a; have := congrFun (hP a) j; simpa [col, ev] using this
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [hent]; simp
  · intro b _ hb; rw [hent, if_neg]; · simp
    intro h; apply hb; rw [h]; simp
  · simp

theorem isPerm_X {a c : Fin n} (h : a < c) {e : ℕ} (hc : (c : ℕ) ≤ e) :
    IsPerm (sem n (Gen.X a c h)) e := by
  refine ⟨Equiv.swap a c, fun q hq => ?_, fun q => ?_⟩
  · have h1 : q ≠ a := by intro hq'; subst hq'; have : (q : ℕ) < c := h; omega
    have h2 : q ≠ c := by intro hq'; subst hq'; omega
    exact Equiv.swap_apply_of_ne_of_ne h1 h2
  · have : col (sem n (Gen.X a c h)) q = twoLevel a c Xmat *ᵥ ev q := by
      rw [← mulVec_ev]; rfl
    rw [this, twoLevel_mulVec h.ne]
    funext j
    simp only [Function.update_apply, ev, Xmat]
    by_cases hqa : q = a
    · subst hqa; simp [Equiv.swap_apply_left]; split_ifs <;> simp_all
    by_cases hqc : q = c
    · subst hqc; simp [Equiv.swap_apply_right]; split_ifs <;> simp_all
    rw [Equiv.swap_apply_of_ne_of_ne hqa hqc]
    split_ifs <;> simp_all

/-- A word of transpositions `X_[a,c]` with `c ≤ e`. -/
def XWord (e : ℕ) (b : Word (Gen n)) : Prop :=
  ∀ x ∈ FreeMonoid.toList b, ∃ a c h, x = Gen.X a c h ∧ (c : ℕ) ≤ e

theorem XWord.isPerm {e : ℕ} {b : Word (Gen n)} (hb : XWord e b) : IsPerm ⟪b⟫ e := by
  induction b using FreeMonoid.inductionOn' with
  | one => simpa using IsPerm.one e
  | mul_of x w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of]
    obtain ⟨a, c, h, rfl, hc⟩ := hb x (by simp)
    exact (isPerm_X h hc).mul (ih fun y hy => hb y (by simp [hy]))

theorem XWord.suffix {e : ℕ} {b v w : Word (Gen n)} (hb : XWord e b) (h : b = v * w) :
    XWord e w := fun x hx => hb x (by rw [h, FreeMonoid.toList_mul]; exact List.mem_append_right _ hx)

theorem XWord.mono {e e' : ℕ} {b : Word (Gen n)} (hb : XWord e b) (he : e ≤ e') : XWord e' b := by
  intro x hx; obtain ⟨a, c, h, hx, hc⟩ := hb x hx; exact ⟨a, c, h, hx, by omega⟩

theorem bXd_XWord : ∀ (j d : ℕ) (h : j + d + 1 < n), XWord (j + d + 1) (bXd (n := n) j d h)
  | j, 0, h => by
    intro x hx
    simp only [bXd, X, FreeMonoid.toList_of, List.mem_singleton] at hx
    exact ⟨_, _, _, hx, le_refl _⟩
  | j, d + 1, h => by
    intro x hx
    simp only [bXd, X, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with (hx | hx) | hx
    · exact ⟨_, _, _, hx, le_refl _⟩
    · obtain ⟨a', c, h', hx, hc⟩ := bXd_XWord j d (by omega) x hx
      exact ⟨a', c, h', hx, by omega⟩
    · exact ⟨_, _, _, hx, le_refl _⟩

theorem bX_XWord (j k : Fin n) (h : j < k) : XWord k (bX j k h) := by
  have := bXd_XWord (n := n) j (k - j - 1) (by have := k.2; have : (j : ℕ) < k := h; omega)
  have hjk : (j : ℕ) < k := h
  refine this.mono ?_
  omega

/-! ### Suffixes of words -/

theorem mul_eq_mul_iff {a b c d : Word (Gen n)} :
    a * b = c * d ↔ (∃ x, c = a * x ∧ b = x * d) ∨ ∃ y, a = c * y ∧ d = y * b := by
  have := @List.append_eq_append_iff _ (FreeMonoid.toList a) (FreeMonoid.toList b)
    (FreeMonoid.toList c) (FreeMonoid.toList d)
  constructor
  · intro h
    rcases this.1 (by rw [← FreeMonoid.toList_mul, ← FreeMonoid.toList_mul, h]) with
      ⟨x, h1, h2⟩ | ⟨y, h1, h2⟩
    · exact Or.inl ⟨FreeMonoid.ofList x, FreeMonoid.toList.injective h1,
        FreeMonoid.toList.injective h2⟩
    · exact Or.inr ⟨FreeMonoid.ofList y, FreeMonoid.toList.injective h1,
        FreeMonoid.toList.injective h2⟩
  · rintro (⟨x, rfl, rfl⟩ | ⟨y, rfl, rfl⟩) <;> simp [mul_assoc]

theorem of_eq_mul_iff {x : Gen n} {v w : Word (Gen n)} :
    FreeMonoid.of x = v * w ↔ (v = 1 ∧ w = FreeMonoid.of x) ∨ (v = FreeMonoid.of x ∧ w = 1) := by
  constructor
  · intro h
    have h' : FreeMonoid.toList v ++ FreeMonoid.toList w = [x] := by
      rw [← FreeMonoid.toList_mul, ← h]; rfl
    rcases List.append_eq_singleton_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨FreeMonoid.toList.injective h1, FreeMonoid.toList.injective h2⟩
    · exact Or.inr ⟨FreeMonoid.toList.injective h1, FreeMonoid.toList.injective h2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- Every state along the word `b` from `u` is `P u` or `P (y u)` for a
permutation `P` fixing the indices above `e`. -/
def SufOK (b : Word (Gen n)) (y : Gen n) (e : ℕ) : Prop :=
  ∀ (u : St n) (v w : Word (Gen n)), b = v * w →
    ∃ P, IsPerm P e ∧ (⟪w⟫ * u = P * u ∨ ⟪w⟫ * u = P * (sem n y * u))

theorem SufOK.of_XWord {b : Word (Gen n)} {e : ℕ} (hb : XWord e b) (y : Gen n) : SufOK b y e :=
  fun _ _ w h => ⟨⟪w⟫, (hb.suffix h).isPerm, Or.inl rfl⟩

theorem SufOK.single (y : Gen n) (e : ℕ) : SufOK (FreeMonoid.of y) y e := by
  intro u v w h
  rcases of_eq_mul_iff.1 h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨1, IsPerm.one e, Or.inr (by simp)⟩
  · exact ⟨1, IsPerm.one e, Or.inl (by simp)⟩

theorem SufOK.conj {π b' : Word (Gen n)} {y y' : Gen n} {e : ℕ} (hπ : XWord e π)
    (hπ2 : ⟪π⟫ * ⟪π⟫ = 1) (hconj : ⟪π⟫ * sem n y' * ⟪π⟫ = sem n y) (hb' : ⟪b'⟫ = sem n y')
    (h : SufOK b' y' e) : SufOK (π * b' * π) y e := by
  intro u v w hvw
  have hP := hπ.isPerm
  have hy : sem n y' * ⟪π⟫ = ⟪π⟫ * sem n y := by
    rw [← hconj, ← mul_assoc, ← mul_assoc, hπ2, one_mul]
  rcases mul_eq_mul_iff.1 hvw with ⟨x, -, hx⟩ | ⟨c', hc', rfl⟩
  · exact ⟨⟪w⟫, (hπ.suffix hx).isPerm, Or.inl rfl⟩
  · rcases mul_eq_mul_iff.1 hc' with ⟨x, -, hx⟩ | ⟨c'', hc'', rfl⟩
    · obtain ⟨P, hPe, hcase⟩ := h (⟪π⟫ * u) x c' hx
      refine ⟨P * ⟪π⟫, hPe.mul hP, ?_⟩
      rw [map_mul, mul_assoc]
      rcases hcase with hc | hc
      · left; rw [hc, mul_assoc]
      · right; rw [hc, ← mul_assoc (sem n y'), hy, mul_assoc, mul_assoc]
    · refine ⟨⟪c''⟫ * ⟪π⟫, ((hπ.suffix hc'').isPerm).mul hP, Or.inr ?_⟩
      rw [map_mul, map_mul, hb', mul_assoc, mul_assoc, ← mul_assoc (sem n y'), hy]
      try simp only [mul_assoc]

/-! ### Levels of permuted states -/

theorem prof_ev (c : Fin n) : prof (ev c) = toLex (0, 0) := by
  have h : HasNum (ev c) 0 (fun a => if a = c then 1 else 0) := by
    intro a; by_cases h : a = c <;> simp [ev, h]
  rw [prof_eq h (lde_eq h (Or.inl rfl)), if_pos rfl]

theorem prof_perm {σ : Equiv.Perm (Fin n)} {v : Fin n → ℂ} (hv : ∃ k w, HasNum v k w) :
    prof (fun j => v (σ.symm j)) = prof v := by
  have hw := num_spec hv
  have hw' : HasNum (fun j => v (σ.symm j)) (lde v) (fun j => num v (σ.symm j)) :=
    fun j => hw (σ.symm j)
  have hl : lde (fun j => v (σ.symm j)) = lde v := by
    apply lde_eq hw'
    rcases Nat.eq_zero_or_pos (lde v) with h0 | hpos
    · exact Or.inl h0
    · obtain ⟨j, hj⟩ := exists_odd hw hpos
      exact Or.inr ⟨σ j, by simpa using hj⟩
  have hcard : (oddSet (fun j => num v (σ.symm j))).card = (oddSet (num v)).card := by
    have : oddSet (fun j => num v (σ.symm j)) = (oddSet (num v)).map σ.toEmbedding := by
      ext a; simp [Finset.mem_map_equiv]
    rw [this, Finset.card_map]
  rw [prof_eq hw' hl, prof_eq hw rfl, hcard]

/-- A permutation fixing the indices above `e` does not raise the level of a
state whose pivot is at least `e`. -/
theorem level_perm_le {P u : St n} {e : ℕ} (hP : IsPerm P e) {p : Fin n} (hp : IsPivot u p)
    (hpe : e ≤ (p : ℕ)) : level (P * u) ≤ level u := by
  obtain ⟨σ, hσ, hcol⟩ := hP
  apply level_le_of_cols hp
  · intro q hq
    rw [col_mul, hp.2 q hq, mulVec_ev, hcol, hσ q (by have : (p : ℕ) < q := hq; omega)]
  · right
    rw [col_mul, perm_mulVec hcol, prof_perm (hasNum_exists u p)]

theorem lex_le_level {u : St n} {p : Fin n} (hp : IsPivot u p) {e : ℕ} (hpe : e ≤ (p : ℕ)) :
    toLex (e + 1, toLex (0, 0)) ≤ level u := by
  rw [level_eq hp, Prod.Lex.toLex_le_toLex]
  rcases hpe.lt_or_eq with h | h
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rw [prof, Prod.Lex.toLex_le_toLex]
    rcases Nat.eq_zero_or_pos (lde (col u p)) with h0 | hpos
    · right; exact ⟨h0.symm, Nat.zero_le _⟩
    · left; exact hpos

/-- A permutation fixing the indices above `e`, applied to a state that is
the identity from column `e` on, gives a level at most `(e + 1, 0, 0)`. -/
theorem level_perm_low {P u : St n} {e : ℕ} (hP : IsPerm P e)
    (hu : ∀ q : Fin n, e ≤ (q : ℕ) → col u q = ev q) :
    level (P * u) ≤ toLex (e + 1, toLex (0, 0)) := by
  obtain ⟨σ, hσ, hcol⟩ := hP
  have hc : ∀ q : Fin n, e ≤ (q : ℕ) → col (P * u) q = ev (σ q) := by
    intro q hq; rw [col_mul, hu q hq, mulVec_ev, hcol]
  by_cases h1 : P * u = 1
  · rw [h1, level_one, Prod.Lex.toLex_le_toLex]
    left; omega
  obtain ⟨p', hp'⟩ := exists_pivot h1
  rw [level_eq hp', Prod.Lex.toLex_le_toLex]
  rcases lt_trichotomy (p' : ℕ) e with h | h | h
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rw [hc p' h.ge, prof_ev]
  · exfalso
    apply hp'.1
    rw [hc p' h.le, hσ p' h]

/-- The extent of a generator (Definition 29): its largest index. -/
def ext : Gen n → ℕ
  | .X _ c _ => c
  | .H _ c _ => c
  | .ω a => a

theorem exists_moved (y : Gen n) (u : St n)
    (hu : ∀ q : Fin n, ext y ≤ (q : ℕ) → col u q = ev q) :
    ∃ q : Fin n, ext y ≤ (q : ℕ) ∧ col (sem n y * u) q ≠ ev q := by
  cases y with
  | X a c h =>
    refine ⟨c, le_refl _, fun heq => ?_⟩
    rw [col_mul, hu c (le_refl _)] at heq
    have := congrFun heq a
    simp only [sm_sem, mat, twoLevel_mulVec h.ne, Function.update_apply, ev, if_neg h.ne,
      Xmat] at this
    simp at this
  | H a c h =>
    refine ⟨c, le_refl _, fun heq => ?_⟩
    rw [col_mul, hu c (le_refl _)] at heq
    have h1 := congrFun heq a
    simp only [sm_sem, mat] at h1
    rw [twoLevel_mulVec h.ne, Function.update_of_ne h.ne, Function.update_self,
      ev_apply_ne h.ne] at h1
    simp [ev, Hmat_00, Hmat_01] at h1
  | ω a =>
    refine ⟨a, le_refl _, fun heq => ?_⟩
    rw [col_mul, hu a (le_refl _)] at heq
    have h1 := congrFun heq a
    simp only [sm_sem, mat] at h1
    rw [oneLevel_mulVec, Function.update_self] at h1
    have h2 : QCert.ω = 1 := by simpa [ev] using h1
    have h3 := ω_sq
    rw [h2, one_pow] at h3
    have := congrArg Complex.re h3
    simp at this

theorem pivot_ge {u : St n} {e : ℕ} (h : ∃ q : Fin n, e ≤ (q : ℕ) ∧ col u q ≠ ev q) :
    ∃ p, IsPivot u p ∧ e ≤ (p : ℕ) := by
  obtain ⟨q, hq, hne⟩ := h
  have hu : u ≠ 1 := by rintro rfl; exact hne (col_one q)
  obtain ⟨p, hp⟩ := exists_pivot hu
  refine ⟨p, hp, ?_⟩
  by_contra hlt
  exact hne (hp.2 q (Fin.lt_def.2 (by omega)))

/-- A permuted state `P u` stays below `L` when `u` and `u'` do and one of
them has pivot at least `e`. -/
theorem level_perm_lt {P u u' : St n} {e : ℕ} (hP : IsPerm P e) {L : ℕ ×ₗ ℕ ×ₗ ℕ}
    (hu : level u < L) (hu' : level u' < L)
    (h : (∃ q : Fin n, e ≤ (q : ℕ) ∧ col u q ≠ ev q) ∨
      ∃ q : Fin n, e ≤ (q : ℕ) ∧ col u' q ≠ ev q) :
    level (P * u) < L := by
  by_cases h1 : ∃ q : Fin n, e ≤ (q : ℕ) ∧ col u q ≠ ev q
  · obtain ⟨p, hp, hpe⟩ := pivot_ge h1
    exact lt_of_le_of_lt (level_perm_le hP hp hpe) hu
  · have h2 := h.resolve_left h1
    push Not at h1
    obtain ⟨p', hp', hpe'⟩ := pivot_ge h2
    exact lt_of_le_of_lt (level_perm_low hP h1) (lt_of_le_of_lt (lex_le_level hp' hpe') hu')

/-! ### Basic words of the generators -/

theorem lift_eq_of_cl {w v : Word (Gen n)} (h : cl w = cl v) : ⟪w⟫ = ⟪v⟫ :=
  derivable_sound (fun _ _ h => sound h) (derivable_iff.2 h)

theorem bX_sq (j k : Fin n) (h : j < k) : ⟪bX j k h⟫ * ⟪bX j k h⟫ = 1 := by
  rw [← map_mul, ← map_one (FreeMonoid.lift (sem n))]
  apply lift_eq_of_cl
  rw [map_mul, cl_bX, e3, map_one]

theorem sufOK_bw (y : Gen n) : SufOK (bw y) y (ext y) := by
  cases y with
  | X j k h => exact SufOK.of_XWord (bX_XWord j k h) _
  | ω j =>
    simp only [bw]
    split_ifs with hj
    · exact SufOK.single _ _
    · refine SufOK.conj (bX_XWord _ _ _) (bX_sq _ _ _) ?_ (FreeMonoid.lift_eval_of _ _)
        (SufOK.single _ _)
      rw [← FreeMonoid.lift_eval_of (sem n) (Gen.ω j), ← FreeMonoid.lift_eval_of (sem n),
        ← map_mul, ← map_mul]
      apply lift_eq_of_cl
      simp only [map_mul, cl_bX, cl_ω]
      exact (gω_pos _ _ _).symm
  | H j k h =>
    have hjk : (j : ℕ) < k := h
    simp only [bw]
    split_ifs with hj hk
    · exact SufOK.single _ _
    · refine SufOK.conj (bX_XWord _ _ _) (bX_sq _ _ _) ?_ (FreeMonoid.lift_eval_of _ _)
        (SufOK.single _ _)
      rw [← FreeMonoid.lift_eval_of (sem n) (Gen.H j k h), ← FreeMonoid.lift_eval_of (sem n),
        ← map_mul, ← map_mul]
      apply lift_eq_of_cl
      simp only [map_mul, cl_bX, cl_H]
      exact ((gH_congr (Fin.ext hj) rfl).trans (gH_zero _ _ _ (Fin.mk_lt_mk.2 (by omega))
        (Fin.mk_lt_mk.2 (by omega)))).symm
    · refine SufOK.conj ((bX_XWord _ _ _).mono (by show (j : ℕ) ≤ (k : ℕ); omega)) (bX_sq _ _ _)
        (y' := Gen.H ⟨0, j.pos⟩ k (Fin.mk_lt_mk.2 (by omega))) ?_ ?_ ?_
      · rw [← FreeMonoid.lift_eval_of (sem n) (Gen.H j k h), ← FreeMonoid.lift_eval_of (sem n),
          ← map_mul, ← map_mul]
        apply lift_eq_of_cl
        simp only [map_mul, cl_bX, cl_H]
        exact (gH_pos _ _ _ _ _).symm
      · rw [← FreeMonoid.lift_eval_of (sem n)]
        apply lift_eq_of_cl
        simp only [map_mul, cl_bX, cl_H]
        exact (gH_zero _ _ _ (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))).symm
      · refine SufOK.conj (bX_XWord _ _ _) (bX_sq _ _ _) ?_ (FreeMonoid.lift_eval_of _ _)
          (SufOK.single _ _)
        rw [← FreeMonoid.lift_eval_of (sem n), ← FreeMonoid.lift_eval_of (sem n),
          ← map_mul, ← map_mul]
        apply lift_eq_of_cl
        simp only [map_mul, cl_bX, cl_H]
        exact (gH_zero _ _ _ (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))).symm

/-- Along a basic path below `L`, given `Step` for basic edges below `L`. -/
theorem path_step_basic (L : ℕ ×ₗ ℕ ×ₗ ℕ)
    (hB : ∀ (u : St n) x, Basic x → level u < L → Step u x) :
    ∀ (w : Word (Gen n)), AllBasic w → ∀ (t : St n), AllBelow L t w →
      Derivable (Rel n) (nw (⟪w⟫ * t) * w) (nw t) := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => intro _ t _; simp only [map_one, one_mul, mul_one]; exact Derivable.refl _
  | mul_of x w ih =>
    intro hb t hw
    have hx : Basic x := hb x (by simp)
    have hwb : AllBasic w := fun y hy => hb y (by simp [hy])
    have h1 : level (⟪w⟫ * t) < L := hw (FreeMonoid.of x) w rfl
    rw [map_mul, FreeMonoid.lift_eval_of, mul_assoc, ← mul_assoc (nw _)]
    exact ((hB _ x hx h1).mul (Derivable.refl w)).trans (ih hwb t hw.tail)

/-- Lemma 30 with its level part (c): `Step` along simple edges below `L`
from `Step` along basic edges below `L`. -/
theorem lift_basic' (L : ℕ ×ₗ ℕ ×ₗ ℕ)
    (hB : ∀ (u : St n) x, Basic x → level u < L → Step u x)
    (u : St n) (y : Gen n) (hu : level u < L) (hyu : level (sem n y * u) < L) : Step u y := by
  have hall : AllBelow L u (bw y) := by
    intro v w hvw
    obtain ⟨P, hP, hcase⟩ := sufOK_bw y u v w hvw
    have hmoved : (∃ q : Fin n, ext y ≤ (q : ℕ) ∧ col u q ≠ ev q) ∨
        ∃ q : Fin n, ext y ≤ (q : ℕ) ∧ col (sem n y * u) q ≠ ev q := by
      by_cases h : ∃ q : Fin n, ext y ≤ (q : ℕ) ∧ col u q ≠ ev q
      · exact Or.inl h
      · push Not at h; exact Or.inr (exists_moved y u h)
    rcases hcase with hc | hc
    · rw [hc]; exact level_perm_lt hP hu hyu hmoved
    · rw [hc]; exact level_perm_lt hP hyu hu hmoved.symm
  have hsem : ⟪bw y⟫ = sem n y := by
    rw [← lift_eq_of_cl (cl_bw y), FreeMonoid.lift_eval_of]
  have := path_step_basic L hB (bw y) (bw_basic y) u hall
  rw [hsem] at this
  exact ((Derivable.refl _).mul (derivable_iff.2 (cl_bw y))).trans this

end

end QCert.Greylyn
