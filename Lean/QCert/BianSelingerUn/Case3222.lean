/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: Case 3.2.2.2 with four odd entries

`G = X_[α,α+1]`, the first two odd entries of the pivot column are `j < ℓ`
with `ℓ = α`, and `w_{α+1}` is odd too; let `ℓ'` be the next odd entry
(Lemma 2.9), so that the four odd entries are `j < ℓ < j' = α+1 < ℓ'`.  By
Lemma 2.3 each is `i^{-e} (1 + γ³ A)`; the diagonal word
`D = i_[j]^e i_[ℓ]^f i_[j']^g i_[ℓ']^h` makes them `1 + γ³ A`, the special
case, whose square is `special_sq` with the states of `chain`.  The square
of `s` is the outer perimeter of the figure of Case 3.2.2.2,
`N' X ∼ E'⁻¹ G'' E N`, from the faces `K† D ∼ E N`, `X D ∼ D' X`,
`K† D' ∼ E' N'`.  In `G''` each `K†_[a,b]` is written `i_[a] i_[b] K_[a,b]`
(a word equal to `K⁷` by (17), (18)), so that every state of the path is
a state of the chain up to a diagonal word.
-/
import QCert.BianSelingerUn.Special
import QCert.BianSelingerUn.Derived3

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

/-! ### Lemma 2.3 -/

/-- Lemma 2.3: an odd Gaussian integer is `i^{-E} (1 + γ³ A)`. -/
theorem exists_normal {g : GaussianInt} (hg : GOdd g) :
    ∃ E : ℕ, E < 4 ∧ ∃ A : GaussianInt, iz ^ E * g = 1 + γz ^ 3 * A := by
  unfold GOdd at hg
  rw [hγ3]
  by_cases hr : g.re % 2 = 1
  · by_cases h1 : (g.re + g.im) % 4 = 1
    · refine ⟨0, by norm_num, ⟨(g.im - (g.re - 1)) / 4, -((g.re - 1) + g.im) / 4⟩, ?_⟩
      ext <;> simp <;> omega
    · refine ⟨2, by norm_num, ⟨(-g.im - (-g.re - 1)) / 4, -((-g.re - 1) + -g.im) / 4⟩, ?_⟩
      ext <;> simp [pow_succ, iz] <;> omega
  · by_cases h1 : (g.re - g.im) % 4 = 1
    · refine ⟨1, by norm_num, ⟨(g.re - (-g.im - 1)) / 4, -((-g.im - 1) + g.re) / 4⟩, ?_⟩
      ext <;> simp [iz] <;> omega
    · refine ⟨3, by norm_num, ⟨(-g.re - (g.im - 1)) / 4, -((g.im - 1) + -g.re) / 4⟩, ?_⟩
      ext <;> simp [pow_succ, iz] <;> omega

theorem re_mod_of_normal {g A : GaussianInt} {E : ℕ} (hE : E < 4)
    (h : iz ^ E * g = 1 + γz ^ 3 * A) (hg : GOdd g) :
    g.re % 2 = if E % 2 = 0 then 1 else 0 := by
  rw [hγ3] at h
  have h1 := congrArg Zsqrtd.re h
  have h2 := congrArg Zsqrtd.im h
  unfold GOdd at hg
  interval_cases E <;> simp [pow_succ, iz] at h1 h2 <;> omega

theorem qexp_of_normal {g g' A A' : GaussianInt} {E E' : ℕ} (hE : E < 4) (hE' : E' < 4)
    (h : iz ^ E * g = 1 + γz ^ 3 * A) (h' : iz ^ E' * g' = 1 + γz ^ 3 * A') (hg : GOdd g)
    (hg' : GOdd g') : qexp g g' = (E + E') % 2 := by
  have e1 := re_mod_of_normal hE h hg
  have e2 := re_mod_of_normal hE' h' hg'
  unfold qexp
  split_ifs at e1 e2 <;> split_ifs <;> omega

theorem gi_pow_congr (x : Fin n) {e e' : ℕ} (h : e % 4 = e' % 4) : gi x ^ e = gi x ^ e' := by
  rw [gi_pow_mod, h, ← gi_pow_mod]

theorem gi_pow_inv (x : Fin n) {e : ℕ} (he : e < 4) : gi x ^ (4 - e) * gi x ^ e = 1 := by
  rw [← pow_add, Nat.sub_add_cancel he.le, e1]

theorem gX_pow_sq (a b : Fin n) (h : a < b) {m : ℕ} (hm : m < 2) :
    gX a b h ^ m * gX a b h ^ m = 1 := by
  interval_cases m
  · simp
  · simp [e2]

theorem tinv {M : Type*} [Monoid M] {u v : M} (h : u * v = 1) (t : M) : u * (v * t) = t := by
  rw [← mul_assoc, h, one_mul]

/-! ### Paths -/

theorem AllBelow.mul {L : ℕ ×ₗ ℕ ×ₗ ℕ} {t : St n} {u v : Word (Gen n)} (hv : AllBelow L t v)
    (hu : AllBelow L (⟪v⟫ * t) u) : AllBelow L t (u * v) := by
  intro x y hxy
  rcases mul_eq_mul_iff.1 hxy with ⟨c, -, hc2⟩ | ⟨c, hc1, hc2⟩
  · exact hv c y hc2
  · rw [hc2, map_mul, mul_assoc]; exact hu x c hc1

theorem level_mon {s t : St n} {p : Fin n} (hs : IsPivot s p) (hk : 0 < lde (col s p))
    (ht : level t < level s) {D : Word (Gen n)} (hD : ∀ x ∈ FreeMonoid.toList D, MonLetter p x) :
    level (⟪D⟫ * t) < level s :=
  allBelow_mon hs ht (cols_of_level_le hs ht.le) hD (Or.inl hk) 1 D (by simp)

theorem lift_iiK (a b : Fin n) (hab : a < b) : ⟪i a * i b * K a b hab⟫ = ⟪K a b hab ^ 7⟫ := by
  apply lift_eq_of_cl
  simp only [map_mul, map_pow, cl_K, cl_i]
  have := tKd a b hab 1
  simp only [mul_one] at this
  rw [this, mul_assoc]

theorem sem_K_eq (a b : Fin n) (hab : a < b) :
    sem n (Gen.K a b hab) = ⟪i a * i a * i a * i b * i b * i b⟫ * ⟪K a b hab ^ 7⟫ := by
  rw [← FreeMonoid.lift_eval_of (sem n), ← map_mul]
  apply lift_eq_of_cl
  simp only [map_mul, map_pow, cl_ofK, cl_K, cl_i]
  have := f22 a b hab 1
  simp only [mul_one] at this
  exact this.trans (by simp only [mul_assoc])

theorem sem_K_Kd (a b : Fin n) (hab : a < b) (u : St n) :
    sem n (Gen.K a b hab) * (⟪K a b hab ^ 7⟫ * u) = u := by
  rw [← mul_assoc, ← FreeMonoid.lift_eval_of (sem n), ← map_mul]
  have : ⟪FreeMonoid.of (Gen.K a b hab) * K a b hab ^ 7⟫ = 1 := by
    rw [← map_one (FreeMonoid.lift (sem n))]
    apply lift_eq_of_cl
    simp only [map_mul, map_pow, cl_ofK, map_one]
    exact gK_mul_pow_seven a b hab
  rw [this, one_mul]

/-- The path `i_[a] i_[b] K_[a,b]` from `v` to `K†_[a,b] v`, both below `s`. -/
theorem allBelow_iiK {s v : St n} {p : Fin n} (hs : IsPivot s p) (hk : 0 < lde (col s p))
    {a b : Fin n} (hab : a < b) (hbp : b ≤ p) (hv : level v < level s)
    (hv' : level (⟪K a b hab ^ 7⟫ * v) < level s) :
    AllBelow (level s) v (i a * i b * K a b hab) := by
  have hap : a ≤ p := hab.le.trans hbp
  have hmon : ∀ D : Word (Gen n), (∀ x ∈ FreeMonoid.toList D, MonLetter p x) →
      level (⟪D⟫ * (⟪K a b hab ^ 7⟫ * v)) < level s := fun D hD => level_mon hs hk hv' hD
  have hM : ∀ x ∈ FreeMonoid.toList (i a * i a * i a * i b * i b * i b), MonLetter p x := by
    intro x hx
    simp only [i, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl
    all_goals first | exact hap | exact hbp
  have l1 : level (sem n (Gen.K a b hab) * v) < level s := by
    rw [sem_K_eq, mul_assoc]; exact hmon _ hM
  have l2 : level (sem n (Gen.i b) * (sem n (Gen.K a b hab) * v)) < level s := by
    rw [sem_K_eq, mul_assoc, ← mul_assoc (sem n (Gen.i b)), ← FreeMonoid.lift_eval_of (sem n),
      ← map_mul]
    apply hmon
    intro x hx
    rw [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hbp
    · exact hM x hx
  apply AllBelow.mul (allBelow_single hv l1)
  rw [FreeMonoid.lift_eval_of]
  apply AllBelow.mul (allBelow_single l1 l2)
  rw [FreeMonoid.lift_eval_of]
  refine allBelow_single l2 ?_
  have e := lift_iiK a b hab
  simp only [map_mul, FreeMonoid.lift_eval_of] at e
  rw [← mul_assoc, ← mul_assoc, e]; exact hv'

theorem hasNum_ipow {u : St n} {q : Fin n} {k : ℕ} {w : Fin n → GaussianInt}
    (h : HasNum (col u q) k w) (x : Fin n) (e : ℕ) :
    HasNum (col (⟪i x ^ e⟫ * u) q) k (Function.update w x (iz ^ e * w x)) := by
  rw [col_mul, sm_lift, matOf_ipow]; exact hasNum_oneLevel h x e

theorem hasNum_ipow' {u : St n} {q : Fin n} {k : ℕ} {w : Fin n → GaussianInt}
    (h : HasNum (col u q) k w) (x : Fin n) (e : ℕ) {g : GaussianInt} (hg : w x = g) :
    HasNum (col (⟪i x ^ e⟫ * u) q) k (Function.update w x (iz ^ e * g)) := by
  rw [← hg]; exact hasNum_ipow h x e

theorem mem_toList_pow {x y : Gen n} {e : ℕ} (h : y ∈ FreeMonoid.toList (FreeMonoid.of x ^ e)) :
    y = x := by
  induction e with
  | zero => simp at h
  | succ e ih =>
    rw [pow_succ, FreeMonoid.toList_mul, List.mem_append, FreeMonoid.toList_of,
      List.mem_singleton] at h
    rcases h with h | h
    · exact ih h
    · exact h

theorem mon_ipow {p x : Fin n} (hx : x ≤ p) (e : ℕ) :
    ∀ y ∈ FreeMonoid.toList (i x ^ e), MonLetter p y := fun y hy => by
  rw [mem_toList_pow hy]; exact hx

theorem mon_Xpow {p a b : Fin n} (hab : a < b) (hb : b ≤ p) (e : ℕ) :
    ∀ y ∈ FreeMonoid.toList (X a b hab ^ e), MonLetter p y := fun y hy => by
  rw [mem_toList_pow hy]; exact hb

theorem mon_mul {p : Fin n} {u v : Word (Gen n)} (hu : ∀ y ∈ FreeMonoid.toList u, MonLetter p y)
    (hv : ∀ y ∈ FreeMonoid.toList v, MonLetter p y) :
    ∀ y ∈ FreeMonoid.toList (u * v), MonLetter p y := by
  intro y hy
  rw [FreeMonoid.toList_mul, List.mem_append] at hy
  rcases hy with hy | hy
  · exact hu y hy
  · exact hv y hy

theorem noK_of_mon {p : Fin n} {w : Word (Gen n)} (hw : ∀ y ∈ FreeMonoid.toList w, MonLetter p y) :
    ∀ x ∈ FreeMonoid.toList w, ∀ a b h, x ≠ Gen.K a b h := by
  intro x hx a b h e; subst e; exact hw _ hx

theorem card_eq_of_prof {v v' : Fin n → ℂ} {k : ℕ} {w w' : Fin n → GaussianInt}
    (hv : HasNum v k w) (hk : lde v = k) (hv' : HasNum v' k w') (hp : prof v' = prof v) :
    (oddSet w').card = (oddSet w).card := by
  have hp' := hp
  rw [prof_eq hv hk] at hp'
  unfold prof at hp'
  have h1 : lde v' = k := (Prod.mk.inj (toLex.injective hp')).1
  rw [prof_eq hv' h1, prof_eq hv hk] at hp
  exact (Prod.mk.inj (toLex.injective hp)).2

theorem lift_mul_apply (u v : Word (Gen n)) (t : St n) : ⟪u * v⟫ * t = ⟪u⟫ * (⟪v⟫ * t) := by
  rw [map_mul, mul_assoc]

/-- The algebra of the outer square of Case 3.2.2.2, from its five faces. -/
theorem square_alg {M : Type*} [Monoid M] {PR x PI PG PE PS k PD PD' PE' : M}
    (F1 : k * PD = PE * PS) (F2 : k * PD' = PE' * PR) (F3 : x * PD = PD' * x)
    (F4 : PG * k = k * x) (F5 : PI * PE' = 1) : PR * x = PI * (PG * (PE * PS)) := by
  rw [← F1, ← mul_assoc PG, F4, mul_assoc k, F3, ← mul_assoc k, F2, ← mul_assoc PI,
    ← mul_assoc PI, F5, one_mul]

set_option maxHeartbeats 4000000 in
/-- Case 3.2.2.2 with `w_{α+1}` odd. -/
theorem case_3222_odd' {s : St n} (hs : s ≠ 1) {a b p : Fin n} (hab : a < b)
    (hb : (b : ℕ) = a + 1) (hp : IsPivot s p) (hbp : b ≤ p) {w : Fin n → GaussianInt}
    (hw : HasNum (col s p) (lde (col s p)) w) (hpos : 0 < lde (col s p)) {j : Fin n}
    (hf : FirstTwo w j a) (hbodd : GOdd (w b))
    (hstep : ∀ u y, level u < level s → level (sem n y * u) < level s → Step u y) :
    Step s (Gen.X a b hab) := by
  obtain ⟨hja, hj, ha, hbefore, hbetween⟩ := hf
  have hnot : ∀ x : Fin n, a < x → x < b → False := fun x h1 h2 => by
    have := Fin.lt_def.1 h1; have := Fin.lt_def.1 h2; omega
  have hjb : j < b := hja.trans hab
  ---- the fourth odd entry `d` (Lemma 2.9)
  obtain ⟨d, hbd, hd, -, hdp⟩ : ∃ d, b < d ∧ GOdd (w d) ∧
      (∀ y, b < y → y < d → ¬ GOdd (w y)) ∧ d ≤ p := by
    have hev : Even (oddSet w).card := even_card_odd (col_unit s p) hw hpos
    have h3 : ({j, a, b} : Finset (Fin n)) ⊆ oddSet w := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact mem_oddSet.2 hj
      · exact mem_oddSet.2 ha
      · exact mem_oddSet.2 hbodd
    have hc3 : ({j, a, b} : Finset (Fin n)).card = 3 :=
      Finset.card_eq_three.2 ⟨j, a, b, hja.ne, hjb.ne, hab.ne, rfl⟩
    have hlt : ({j, a, b} : Finset (Fin n)).card < (oddSet w).card := by
      have := Finset.card_le_card h3
      obtain ⟨r, hr⟩ := hev
      omega
    obtain ⟨x, hx, hxn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hbx : b < x := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxn
      obtain ⟨hxj, hxa, hxb⟩ := hxn
      have hxo := mem_oddSet.1 hx
      rcases lt_trichotomy x j with h | h | h
      · exact absurd hxo (hbefore x h)
      · exact absurd h hxj
      rcases lt_trichotomy x a with h' | h' | h'
      · exact absurd hxo (hbetween x h h')
      · exact absurd h' hxa
      rcases lt_trichotomy x b with h'' | h'' | h''
      · exact (hnot x h' h'').elim
      · exact absurd h'' hxb
      · exact h''
    have hT : ((oddSet w).filter (fun y => b < y)).Nonempty := ⟨x, Finset.mem_filter.2 ⟨hx, hbx⟩⟩
    have hmin := Finset.min'_mem _ hT
    rw [Finset.mem_filter] at hmin
    refine ⟨_, hmin.2, mem_oddSet.1 hmin.1, fun y hy hy' hyo => ?_, ?_⟩
    · exact absurd (Finset.min'_le _ y (Finset.mem_filter.2 ⟨mem_oddSet.2 hyo, hy⟩))
        (not_le.2 hy')
    · by_contra hlt'
      have h0 := hasNum_zero_of_entry hp hw (not_le.1 hlt')
      have h4 := mem_oddSet.1 hmin.1
      rw [h0] at h4; exact absurd h4 (by decide)
  have had : a < d := hab.trans hbd
  have hjd : j < d := hja.trans had
  have hap : a ≤ p := hab.le.trans hbp
  have hjp : j ≤ p := hja.le.trans hap
  ---- Lemma 2.3 for the four odd entries
  obtain ⟨Ej, hEj, Aj, hAj⟩ := exists_normal hj
  obtain ⟨Ea, hEa, Aa, hAa⟩ := exists_normal ha
  obtain ⟨Eb, hEb, Ab, hAb⟩ := exists_normal hbodd
  obtain ⟨Ed, hEd, Ad, hAd⟩ := exists_normal hd
  ---- the syllables of `s` and `r`
  have hsyl : syl s = K j a hja ^ 7 * i a ^ qexp (w j) (w a) :=
    (syl_eq hp).trans (sylCol_K hw hpos rfl ⟨hja, hj, ha, hbefore, hbetween⟩)
  have hwX := hasNum_sem_X hw hab
  have wXj : Function.update (Function.update w a (w b)) b (w a) j = w j := by
    rw [Function.update_of_ne hjb.ne, Function.update_of_ne hja.ne]
  have wXa : Function.update (Function.update w a (w b)) b (w a) a = w b := by
    rw [Function.update_of_ne hab.ne, Function.update_self]
  have hfr : FirstTwo (Function.update (Function.update w a (w b)) b (w a)) j a := by
    refine ⟨hja, by rw [wXj]; exact hj, by rw [wXa]; exact hbodd, ?_, ?_⟩
    · intro x hx
      rw [Function.update_of_ne ((hx.trans hjb).ne), Function.update_of_ne ((hx.trans hja).ne)]
      exact hbefore x hx
    · intro x hx hx'
      rw [Function.update_of_ne ((hx'.trans hab).ne), Function.update_of_ne hx'.ne]
      exact hbetween x hx hx'
  have hrp : IsPivot (sem n (Gen.X a b hab) * s) p :=
    isPivot_sem hp hbp (by rw [← col_sem]; exact ne_ev_of_odd hwX hpos ⟨j, hfr.2.1⟩ p)
  have hsylr : syl (sem n (Gen.X a b hab) * s) = K j a hja ^ 7 * i a ^ qexp (w j) (w b) := by
    rw [syl_eq hrp, sylCol_K hwX hpos (lde_of_odd hwX j hfr.2.1) hfr, K_congr hfr.1 hja rfl rfl,
      wXj, wXa]
  ---- exponents
  rw [qexp_of_normal hEj hEa hAj hAa hj ha] at hsyl
  rw [qexp_of_normal hEj hEb hAj hAb hj hbodd] at hsylr
  obtain ⟨q, hq⟩ : ∃ q, q = (Ej + Ea) % 2 := ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q', q' = (Ej + Eb) % 2 := ⟨_, rfl⟩
  rw [← hq] at hsyl
  rw [← hq'] at hsylr
  obtain ⟨m, hm⟩ : ∃ m, m = ((Ea + 8 - Ej - q) % 4) / 2 := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m', m' = ((Eb + 8 - Ej - q') % 4) / 2 := ⟨_, rfl⟩
  have hmE : (Ej + 2 * m + q) % 4 = Ea % 4 := by omega
  have hmE' : (Ej + 2 * m' + q') % 4 = Eb % 4 := by omega
  have hm2 : m' < 2 := by omega
  ---- the words
  obtain ⟨Dw, hDw⟩ : ∃ D : Word (Gen n), D = i j ^ Ej * i a ^ Ea * i b ^ Eb * i d ^ Ed :=
    ⟨_, rfl⟩
  obtain ⟨D'w, hD'w⟩ : ∃ D : Word (Gen n), D = i j ^ Ej * i a ^ Eb * i b ^ Ea * i d ^ Ed :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ D : Word (Gen n),
      D = i j ^ Ej * i a ^ Ej * X j a hja ^ m * i b ^ Eb * i d ^ Ed := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ D : Word (Gen n),
      D = i j ^ Ej * i a ^ Ej * X j a hja ^ m' * i b ^ Ea * i d ^ Ed := ⟨_, rfl⟩
  obtain ⟨Einv, hEinv⟩ : ∃ D : Word (Gen n),
      D = i d ^ (4 - Ed) * i b ^ (4 - Ea) * X j a hja ^ m' * i a ^ (4 - Ej) * i j ^ (4 - Ej) :=
    ⟨_, rfl⟩
  obtain ⟨G'', hG''⟩ : ∃ D : Word (Gen n), D = K b d hbd * K j b hjb * K a d had * X a b hab *
      (i a * i d * K a d had) * (i j * i b * K j b hjb) * (i b * i d * K b d hbd) := ⟨_, rfl⟩
  ---- commutations
  have cKb : Commute (gK j a hja) (gi b) := (e6 b j a hja hjb.ne' hab.ne').symm
  have cKd : Commute (gK j a hja) (gi d) := (e6 d j a hja hjd.ne' had.ne').symm
  have cab : Commute (gi a) (gi b) := e4 a b hab.ne
  have cad : Commute (gi a) (gi d) := e4 a d had.ne
  have cXj : Commute (gX a b hab) (gi j) := (e5 j a b hab hja.ne hjb.ne).symm
  have cXd : Commute (gX a b hab) (gi d) := (e5 d a b hab had.ne' hbd.ne').symm
  ---- the faces
  have F1 : gK j a hja ^ 7 * cl Dw = cl E * cl (syl s) := by
    rw [hsyl, hE, hDw]
    simp only [map_mul, map_pow, cl_K, cl_X, cl_i]
    have hc : Commute (gK j a hja ^ 7 * gi a ^ q) (gi b ^ Eb * gi d ^ Ed) :=
      (((cKb.pow_left 7).mul_left (cab.pow_left q)).pow_right Eb).mul_right
        (((cKd.pow_left 7).mul_left (cad.pow_left q)).pow_right Ed)
    calc _ = gK j a hja ^ 7 * (gi j ^ Ej * gi a ^ (Ej + 2 * m + q)) * (gi b ^ Eb * gi d ^ Ed) := by
          rw [gi_pow_congr a hmE.symm]; simp only [mul_assoc]
      _ = gi j ^ Ej * gi a ^ Ej * gX j a hja ^ m *
            ((gK j a hja ^ 7 * gi a ^ q) * (gi b ^ Eb * gi d ^ Ed)) := by
          rw [face j a hja Ej m q]; simp only [mul_assoc]
      _ = _ := by rw [hc.eq]; simp only [mul_assoc]
  have F2 : gK j a hja ^ 7 * cl D'w = cl E' * cl (syl (sem n (Gen.X a b hab) * s)) := by
    rw [hsylr, hE', hD'w]
    simp only [map_mul, map_pow, cl_K, cl_X, cl_i]
    have hc : Commute (gK j a hja ^ 7 * gi a ^ q') (gi b ^ Ea * gi d ^ Ed) :=
      (((cKb.pow_left 7).mul_left (cab.pow_left q')).pow_right Ea).mul_right
        (((cKd.pow_left 7).mul_left (cad.pow_left q')).pow_right Ed)
    calc _ = gK j a hja ^ 7 * (gi j ^ Ej * gi a ^ (Ej + 2 * m' + q')) * (gi b ^ Ea * gi d ^ Ed) := by
          rw [gi_pow_congr a hmE'.symm]; simp only [mul_assoc]
      _ = gi j ^ Ej * gi a ^ Ej * gX j a hja ^ m' *
            ((gK j a hja ^ 7 * gi a ^ q') * (gi b ^ Ea * gi d ^ Ed)) := by
          rw [face j a hja Ej m' q']; simp only [mul_assoc]
      _ = _ := by rw [hc.eq]; simp only [mul_assoc]
  have F3 : gX a b hab * cl Dw = cl D'w * gX a b hab := by
    rw [hDw, hD'w]
    simp only [map_mul, map_pow, cl_i]
    have hsc : SemiconjBy (gX a b hab) (gi j ^ Ej * gi a ^ Ea * gi b ^ Eb * gi d ^ Ed)
        (gi j ^ Ej * gi b ^ Ea * gi a ^ Eb * gi d ^ Ed) :=
      ((SemiconjBy.mul_right (cXj.pow_right Ej) ((sc_Xi a b hab).pow_right Ea)).mul_right
        ((sc_Xi' a b hab).pow_right Eb)).mul_right (cXd.pow_right Ed)
    rw [hsc.eq, mul_assoc (gi j ^ Ej) (gi b ^ Ea), (Commute.pow_pow cab.symm Ea Eb).eq, ← mul_assoc]
  have iik : ∀ (x y : Fin n) (h : x < y), gi x * gi y * gK x y h = gK x y h ^ 7 := by
    intro x y h
    have := tKd x y h 1
    simp only [mul_one] at this
    rw [this, mul_assoc]
  have F4 : cl G'' * gK j a hja ^ 7 = gK j a hja ^ 7 * gX a b hab := by
    rw [hG'']
    simp only [map_mul, cl_K, cl_X, cl_i]
    rw [iik a d had, iik j b hjb, iik b d hbd]
    exact (special_sq j a b d hja hab hbd).symm
  have F5 : cl Einv * cl E' = 1 := by
    rw [hEinv, hE']
    simp only [map_mul, map_pow, cl_i, cl_X]
    simp only [mul_assoc]
    rw [tinv (gi_pow_inv j hEj), tinv (gi_pow_inv a hEj), tinv (gX_pow_sq j a hja hm2),
      tinv (gi_pow_inv b hEa), gi_pow_inv d hEd]
  ---- the relation of the square
  have hrel : cl (syl (sem n (Gen.X a b hab) * s) * FreeMonoid.of (Gen.X a b hab)) =
      cl (Einv * G'' * E * syl s) := by
    rw [map_mul cl (syl _) (FreeMonoid.of _), cl_ofX,
      show Einv * G'' * E * syl s = Einv * (G'' * (E * syl s)) by simp only [mul_assoc],
      map_mul cl Einv, map_mul cl G'', map_mul cl E]
    exact square_alg F1 F2 F3 F4 F5
  ---- the states of the special chains, `s' = D s` and `r' = X s'`
  obtain ⟨s', hs'⟩ : ∃ t : St n, t = ⟪Dw⟫ * s := ⟨_, rfl⟩
  obtain ⟨r', hr'⟩ : ∃ t : St n, t = sem n (Gen.X a b hab) * s' := ⟨_, rfl⟩
  have monD : ∀ y ∈ FreeMonoid.toList Dw, MonLetter p y := by
    rw [hDw]
    exact mon_mul (mon_mul (mon_mul (mon_ipow hjp Ej) (mon_ipow hap Ea)) (mon_ipow hbp Eb))
      (mon_ipow hdp Ed)
  have hs'c : ∀ q, p < q → col s' q = ev q := by
    rw [hs']; exact mon_cols hp.2 Dw monD
  have hr'c : ∀ q, p < q → col r' q = ev q := by
    intro q hq
    have := mon_cols hs'c (X a b hab) (fun y hy => by
      rw [FreeMonoid.toList_of, List.mem_singleton] at hy; rw [hy]; exact hbp) q hq
    rwa [FreeMonoid.lift_eval_of, ← hr'] at this
  -- the numerator of `s'`
  have hD1 := hasNum_ipow hw d Ed
  have hD2 := hasNum_ipow' hD1 b Eb (g := w b) (Function.update_of_ne hbd.ne _ _)
  have hD3 := hasNum_ipow' hD2 a Ea (g := w a)
    (by rw [Function.update_of_ne hab.ne, Function.update_of_ne had.ne])
  have hD4 := hasNum_ipow' hD3 j Ej (g := w j)
    (by rw [Function.update_of_ne hja.ne, Function.update_of_ne hjb.ne,
      Function.update_of_ne hjd.ne])
  have hs'' : ⟪i j ^ Ej⟫ * (⟪i a ^ Ea⟫ * (⟪i b ^ Eb⟫ * (⟪i d ^ Ed⟫ * s))) = s' := by
    rw [hs', hDw]; simp only [map_mul, mul_assoc]
  rw [hs''] at hD4
  obtain ⟨wD, hwD⟩ : ∃ f : Fin n → GaussianInt, f = Function.update (Function.update
      (Function.update (Function.update w d (iz ^ Ed * w d)) b (iz ^ Eb * w b)) a
      (iz ^ Ea * w a)) j (iz ^ Ej * w j) := ⟨_, rfl⟩
  rw [← hwD] at hD4
  have eDj : wD j = 1 + γz ^ 3 * Aj := by rw [hwD, Function.update_self]; exact hAj
  have eDa : wD a = 1 + γz ^ 3 * Aa := by
    rw [hwD, Function.update_of_ne hja.ne', Function.update_self]; exact hAa
  have eDb : wD b = 1 + γz ^ 3 * Ab := by
    rw [hwD, Function.update_of_ne hjb.ne', Function.update_of_ne hab.ne', Function.update_self]
    exact hAb
  have eDd : wD d = 1 + γz ^ 3 * Ad := by
    rw [hwD, Function.update_of_ne hjd.ne', Function.update_of_ne had.ne',
      Function.update_of_ne hbd.ne', Function.update_self]
    exact hAd
  have hprofs' : prof (col s' p) = prof (col s p) := by
    rw [hs']; exact mon_prof p Dw (noK_of_mon monD)
  have hcardD : (oddSet wD).card = (oddSet w).card := card_eq_of_prof hw rfl hD4 hprofs'
  -- the numerator of `r'`
  have hR := hasNum_sem_X hD4 hab
  rw [← hr'] at hR
  have eRj : Function.update (Function.update wD a (wD b)) b (wD a) j = 1 + γz ^ 3 * Aj := by
    rw [Function.update_of_ne hjb.ne, Function.update_of_ne hja.ne]; exact eDj
  have eRa : Function.update (Function.update wD a (wD b)) b (wD a) a = 1 + γz ^ 3 * Ab := by
    rw [Function.update_of_ne hab.ne, Function.update_self]; exact eDb
  have eRb : Function.update (Function.update wD a (wD b)) b (wD a) b = 1 + γz ^ 3 * Aa := by
    rw [Function.update_self]; exact eDa
  have eRd : Function.update (Function.update wD a (wD b)) b (wD a) d = 1 + γz ^ 3 * Ad := by
    rw [Function.update_of_ne hbd.ne', Function.update_of_ne had.ne']; exact eDd
  have hprofr' : prof (col r' p) = prof (col s p) := by
    rw [hr', prof_sem_X, hprofs']
  have hcardR := card_eq_of_prof hw rfl hR hprofr'
  ---- the two special chains
  have CS := chain hp hw hs'c hD4 hcardD hja hab hbd hjb had hdp eDj eDa eDb eDd
  have CR := chain hp hw hr'c hR hcardR hja hab hbd hjb had hdp eRj eRa eRb eRd
  ---- (27) on the states
  have hX4 : sem n (Gen.X a b hab) * (⟪K a d had ^ 7⟫ * (⟪K j b hjb ^ 7⟫ * (⟪K b d hbd ^ 7⟫ *
      (⟪K j a hja ^ 7⟫ * s')))) = ⟪K a d had ^ 7⟫ * (⟪K j b hjb ^ 7⟫ * (⟪K b d hbd ^ 7⟫ *
      (⟪K j a hja ^ 7⟫ * r'))) := by
    have e : ⟪K a d had ^ 7 * K j b hjb ^ 7 * K b d hbd ^ 7 * K j a hja ^ 7 * X a b hab⟫ =
        ⟪X a b hab * (K a d had ^ 7 * K j b hjb ^ 7 * K b d hbd ^ 7 * K j a hja ^ 7)⟫ := by
      apply lift_eq_of_cl
      simp only [map_mul, map_pow, cl_K, cl_X]
      exact f27 j a b d hja hab hbd
    simp only [map_mul, FreeMonoid.lift_eval_of] at e
    calc _ = (sem n (Gen.X a b hab) * (⟪K a d had ^ 7⟫ * ⟪K j b hjb ^ 7⟫ * ⟪K b d hbd ^ 7⟫ *
            ⟪K j a hja ^ 7⟫)) * s' := by simp only [mul_assoc]
      _ = (⟪K a d had ^ 7⟫ * ⟪K j b hjb ^ 7⟫ * ⟪K b d hbd ^ 7⟫ * ⟪K j a hja ^ 7⟫ *
            sem n (Gen.X a b hab)) * s' := by rw [e]
      _ = _ := by rw [hr']; simp only [mul_assoc]
  ---- the path `G''` from `K† s'` to `K† r'`
  have hG : AllBelow (level s) (⟪K j a hja ^ 7⟫ * s') G'' := by
    rw [hG'']
    refine AllBelow.mul (allBelow_iiK hp hpos hbd hdp CS.1 CS.2.1) ?_
    rw [lift_iiK]
    refine AllBelow.mul (allBelow_iiK hp hpos hjb hbp CS.2.1 CS.2.2.1) ?_
    rw [lift_iiK]
    refine AllBelow.mul (allBelow_iiK hp hpos had hdp CS.2.2.1 CS.2.2.2) ?_
    rw [lift_iiK]
    refine AllBelow.mul (allBelow_single CS.2.2.2 ((congrArg level hX4).trans_lt CR.2.2.2)) ?_
    rw [FreeMonoid.lift_eval_of (sem n) (Gen.X a b hab), hX4]
    refine AllBelow.mul (allBelow_single CR.2.2.2
      ((congrArg level (sem_K_Kd a d had _)).trans_lt CR.2.2.1)) ?_
    rw [FreeMonoid.lift_eval_of (sem n) (Gen.K a d had), sem_K_Kd]
    refine AllBelow.mul (allBelow_single CR.2.2.1
      ((congrArg level (sem_K_Kd j b hjb _)).trans_lt CR.2.1)) ?_
    rw [FreeMonoid.lift_eval_of (sem n) (Gen.K j b hjb), sem_K_Kd]
    exact allBelow_single CR.2.1 ((congrArg level (sem_K_Kd b d hbd _)).trans_lt CR.1)
  have hF4' : cl (G'' * K j a hja ^ 7) = cl (K j a hja ^ 7 * X a b hab) := by
    rw [map_mul cl G'', map_mul cl (K j a hja ^ 7), map_pow, cl_K, cl_X]; exact F4
  have hG1 : ⟪G''⟫ * (⟪K j a hja ^ 7⟫ * s') = ⟪K j a hja ^ 7⟫ * r' := by
    rw [← lift_mul_apply G'' (K j a hja ^ 7) s', lift_eq_of_cl hF4',
      lift_mul_apply (K j a hja ^ 7) (X a b hab) s', FreeMonoid.lift_eval_of (sem n) (Gen.X a b hab),
      ← hr']
  ---- the whole path
  have hAB : AllBelow (level s) (⟪syl s⟫ * s) (Einv * G'' * E) := by
    have monE : ∀ y ∈ FreeMonoid.toList E, MonLetter p y := by
      rw [hE]
      exact mon_mul (mon_mul (mon_mul (mon_mul (mon_ipow hjp Ej) (mon_ipow hap Ej))
        (mon_Xpow hja hap m)) (mon_ipow hbp Eb)) (mon_ipow hdp Ed)
    have monEinv : ∀ y ∈ FreeMonoid.toList Einv, MonLetter p y := by
      rw [hEinv]
      exact mon_mul (mon_mul (mon_mul (mon_mul (mon_ipow hdp _) (mon_ipow hbp _))
        (mon_Xpow hja hap m')) (mon_ipow hap _)) (mon_ipow hjp _)
    refine AllBelow.mul (allBelow_mon' hp hs monE (Or.inl hpos)) ?_
    have h1 : ⟪E⟫ * (⟪syl s⟫ * s) = ⟪K j a hja ^ 7⟫ * s' := by
      have hF1 : cl (K j a hja ^ 7 * Dw) = cl (E * syl s) := by
        rw [map_mul cl (K j a hja ^ 7), map_pow, cl_K, map_mul cl E]; exact F1
      rw [← lift_mul_apply E (syl s) s, ← lift_eq_of_cl hF1, lift_mul_apply (K j a hja ^ 7) Dw s,
        hs']
    rw [h1]
    refine AllBelow.mul hG ?_
    rw [hG1]
    exact allBelow_mon hp CR.1 (cols_Kd hr'c hja hap) monEinv (Or.inl hpos)
  exact step_sq hs hrp.ne_one (Einv * G'' * E) hrel hAB hstep

end

end QCert.BianSelingerUn
