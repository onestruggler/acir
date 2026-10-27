/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.20, Subcase 1.2.3: `X_[x,x+1]` on two of the first four odd entries

Then `{x, x+1}` is `{a,b}`, `{b,c}` or `{c,d}`, `G s` has the same first
four odd entries with the signs of `x` and `x + 1` exchanged, and the square
is closed by `(−1)_[d] (−1)_[b] X_[b,d]`, `X_[b,c]` and `X_[b,d]`
respectively: `K X_[x,x+1] ≈ P K` is (4a), (A.11c) and (4c) read backwards
(`rev_derivable`: every generator is an involution).
-/
import QCert.LiRossSelinger.CaseZero

namespace QCert.LiRossSelinger

open QCert

variable {n : ℕ}

/-! ## Reversing a derivation -/

theorem self_inv (l : List (Gen n)) :
    Derivable (Table1 n) (FreeMonoid.ofList (l ++ l.reverse)) 1 := by
  induction l with
  | nil => exact Derivable.refl _
  | cons g l ih =>
    have e : FreeMonoid.ofList ((g :: l) ++ (g :: l).reverse) =
        FreeMonoid.of g * FreeMonoid.ofList (l ++ l.reverse) * FreeMonoid.of g := by
      simp [List.reverse_cons, FreeMonoid.ofList_append, mul_assoc]
    rw [e]
    exact (((Derivable.refl _).mul ih).mul (Derivable.refl _)).trans
      ((deq (by simp)).trans (sq_derivable g))

theorem self_inv' (l : List (Gen n)) :
    Derivable (Table1 n) (FreeMonoid.ofList (l.reverse ++ l)) 1 := by
  simpa using self_inv l.reverse

/-- Every generator is an involution, so a derivation can be read backwards. -/
theorem rev_derivable {l l' : List (Gen n)}
    (h : Derivable (Table1 n) (FreeMonoid.ofList l) (FreeMonoid.ofList l')) :
    Derivable (Table1 n) (FreeMonoid.ofList l.reverse) (FreeMonoid.ofList l'.reverse) := by
  have e1 : Derivable (Table1 n) (FreeMonoid.ofList l.reverse)
      (FreeMonoid.ofList l.reverse * FreeMonoid.ofList (l' ++ l'.reverse)) := by
    have := (Derivable.refl (FreeMonoid.ofList l.reverse)).mul (self_inv l').symm
    rwa [mul_one] at this
  have e2 : Derivable (Table1 n)
      (FreeMonoid.ofList l.reverse * FreeMonoid.ofList (l' ++ l'.reverse))
      (FreeMonoid.ofList (l.reverse ++ l) * FreeMonoid.ofList l'.reverse) := by
    simp only [FreeMonoid.ofList_append]
    have := ((Derivable.refl (FreeMonoid.ofList l.reverse)).mul h.symm).mul
      (Derivable.refl (FreeMonoid.ofList l'.reverse))
    exact (deq (by simp only [mul_assoc])).trans this
  have e3 := (self_inv' l).mul (Derivable.refl (FreeMonoid.ofList l'.reverse))
  rw [one_mul] at e3
  exact e1.trans (e2.trans e3)

/-- (A.11c): `X_[b,c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,c]`. -/
theorem ksym2 {a b c d : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b c h₂, Gen.k a b c d h₁ h₂ h₃])
      (FreeMonoid.ofList [Gen.k a b c d h₁ h₂ h₃, Gen.x b c h₂]) := by
  have h4b : Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b c h₂, Gen.k a b c d h₁ h₂ h₃])
      (FreeMonoid.ofList [Gen.neg a, Gen.k a b c d h₁ h₂ h₃, Gen.neg a, Gen.k a b c d h₁ h₂ h₃,
        Gen.neg a]) := Derivable.of (Table1.r4b a b c d h₁ h₂ h₃)
  exact h4b.trans (rev_derivable h4b).symm

/-! ## Signs and signed permutations -/

theorem negs_perm {l₁ l₂ : List (Fin n)} (h : l₁.Perm l₂) :
    Derivable (Table1 n) (FreeMonoid.ofList (l₁.map Gen.neg)) (FreeMonoid.ofList (l₂.map Gen.neg)) := by
  induction h with
  | nil => exact Derivable.refl _
  | cons x _ ih =>
    simp only [List.map_cons, FreeMonoid.ofList_cons]
    exact (Derivable.refl _).mul ih
  | swap x y l =>
    simp only [List.map_cons, FreeMonoid.ofList_cons]
    have := (neg_comm y x).mul (Derivable.refl (FreeMonoid.ofList (l.map Gen.neg)))
    exact (deq (by simp only [mul_assoc])).trans (this.trans (deq (by simp only [mul_assoc])))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A sign or an exchange below the pivot index `J` of `s`, at a state `t`
below `s` whose later columns are fixed, stays below `s` (`k > 0`). -/
theorem level_signed_lt {s t : O_ZHalf n} (hs : s ≠ 1) (hk : 0 < lde s)
    (hJ : FixCols (mat t) (pivotJ s)) (hlt : level t < level s) {g : Gen n}
    (hg : g.tag ≠ 2) (hb : extent g < pivotJ s) : level (sem n g * t) < level s := by
  have hU := pivot_pos hs
  have hfix : FixCols (mat (sem n g * t)) (pivotJ s) := by
    intro i hi r
    have := col_unit_of_avoid [g] (mat t) i (hJ i hi) (by
      intro g' hg'; rw [List.mem_singleton] at hg'; rw [hg']
      exact avoids_of_extent (lt_of_lt_of_le hb hi)) r
    rwa [show mat (sem n g * t) = ([g].map genMat).prod * mat t by
      rw [← lift_single, mat_word]]
  have hle := pivotJ_le_of _ hfix
  rcases Nat.lt_or_eq_of_le hle with hp | hp
  · rw [level_eq_mk s hU]
    unfold level
    split_ifs
    · rw [mkLevel_lt_iff]; left; exact hU
    · rw [mkLevel_lt_iff]; left; exact hp
  -- the pivot index of `g t` is that of `s`
  by_cases htJ : pivotJ t = pivotJ s
  · -- `g` keeps the odd entries of `t`
    have hU' : 0 < pivotJ t := by rw [htJ]; exact hU
    have hbt : extent g < pivotJ t := by rw [htJ]; exact hb
    refine lt_of_le_of_lt ?_ hlt
    have hl : BelowJ (pivotJ t) [g] := by
      intro g' hg'; rw [List.mem_singleton] at hg'; rw [hg']; exact hbt
    by_cases hu : IsUnitAt (wact [g] (pcol t)) (pidx t hU')
    · have := pivot_word_lt t hU' [g] hl hu
      rw [lift_single] at this
      exact (level_lt_of hU' (Or.inl this)).le
    obtain ⟨h1, h2⟩ := pcol_word t hU' [g] hl hu
    rw [lift_single] at h1
    rw [lift_single, wact_single] at h2
    have hV : 0 < pivotJ (sem n g * t) := by rw [h1]; exact hU'
    -- the integer column of `g t` at the scale of `t`
    obtain ⟨u', hc', hodd⟩ : ∃ u' : Fin n → ℤ, IsCol (pcol (sem n g * t)) (lde t) u' ∧
        ∃ e : Fin n ≃ Fin n, ∀ r, (Odd (u' r) ↔ Odd (wint t (e r))) := by
      cases g with
      | neg z =>
        refine ⟨_, by rw [h2]; exact isCol_neg (isCol_pcol t) z, Equiv.refl _, fun r => ?_⟩
        simp only [Equiv.refl_apply]; split_ifs <;> simp
      | x x y hxy =>
        exact ⟨_, by rw [h2]; exact isCol_x (isCol_pcol t) hxy, Equiv.swap x y, fun r => Iff.rfl⟩
      | k _ _ _ _ _ _ _ => exact absurd rfl hg
    obtain ⟨e, he⟩ := hodd
    rcases Nat.eq_zero_or_pos (lde t) with hk0 | hk0
    · have hl0 : lde (sem n g * t) = 0 := Nat.le_zero.1 (hk0 ▸ lde_le _ hc'.intAt)
      rw [level_eq_mk _ hV, level_eq_mk t hU', h1, hl0, hk0]
      unfold nodd; rw [if_pos hl0, if_pos hk0]
    · obtain ⟨r, hr⟩ : ∃ r, r ∈ oddS t := by
        have := card_oddS t hU' hk0
        exact Finset.card_pos.1 (by omega)
      have hr' : Odd (u' (e.symm r)) := by rw [he, Equiv.apply_symm_apply]; exact (mem_oddS_iff r).1 hr
      have hl' := lde_eq hc' hk0 ⟨_, hr'⟩
      rw [← hl'] at hc'
      have hcard : (Finset.univ.filter fun r => Odd (u' r)).card =
          (Finset.univ.filter fun r => Odd (wint t r)).card := by
        apply Finset.card_bij (fun r _ => e r)
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact (he r).1 hr
        · intro r₁ _ r₂ _ h; exact e.injective h
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact ⟨e.symm r, (he _).2 (by rwa [Equiv.apply_symm_apply]), by simp⟩
      have hnt : nodd t = (Finset.univ.filter fun r => Odd (wint t r)).card := by
        unfold nodd; rw [if_neg (by omega), oddSet_eq (isCol_pcol t)]
      rw [level_eq_mk _ hV, level_eq_mk t hU', h1, hl', nodd_eq hc' (by rw [hl']; exact hk0),
        hcard, hnt]
  · -- `t` has a smaller pivot index: its column at `j` is `e_j`
    have htlt : pivotJ t < pivotJ s := lt_of_le_of_ne (pivotJ_le_of t hJ) htJ
    have hcol : ∀ r, mat t r (pidx s hU) = if r = pidx s hU then 1 else 0 :=
      fixCols_pivotJ t _ (by simp [pidx_val]; omega)
    have hV : 0 < pivotJ (sem n g * t) := by rw [hp]; exact hU
    have hcolV : pcol (sem n g * t) = gact g (fun r => if r = pidx s hU then 1 else 0) := by
      funext r
      rw [pivot_same hU hfix hp r]
      have e := congrFun (colv_word [g] (mat t) (pidx s hU)) r
      rw [← mat_word, lift_single] at e
      simp only [colv] at e
      rw [e, wact_single]
      congr 1
      funext r'; exact hcol r'
    have hint : IntAt (pcol (sem n g * t)) 0 := by
      intro r
      rw [hcolV]
      cases g with
      | neg z =>
        refine ⟨if r = z then -(if r = pidx s hU then 1 else 0) else
          (if r = pidx s hU then 1 else 0), ?_⟩
        simp only [gact, pow_zero, one_mul]
        push_cast
        split_ifs <;> simp
      | x x y hxy =>
        refine ⟨if Equiv.swap x y r = pidx s hU then 1 else 0, ?_⟩
        simp only [gact, pow_zero, one_mul]
        push_cast
        split_ifs <;> simp
      | k _ _ _ _ _ _ _ => exact absurd rfl hg
    have hl0 : lde (sem n g * t) = 0 := Nat.le_zero.1 (lde_le _ hint)
    rw [level_eq_mk _ hV, level_eq_mk s hU, hp, hl0, mkLevel_lt_iff]
    right; exact ⟨rfl, Or.inl hk⟩

theorem fixCols_gen {t : O_ZHalf n} {J : ℕ} (hJ : FixCols (mat t) J) {g : Gen n}
    (hb : extent g < J) : FixCols (mat (sem n g * t)) J := by
  intro i hi r
  have := col_unit_of_avoid [g] (mat t) i (hJ i hi) (by
    intro g' hg'; rw [List.mem_singleton] at hg'; rw [hg']
    exact avoids_of_extent (lt_of_lt_of_le hb hi)) r
  rwa [show mat (sem n g * t) = ([g].map genMat).prod * mat t by rw [← lift_single, mat_word]]

theorem le_pidx_of_odd {s : O_ZHalf n} (hs : s ≠ 1) {r : Fin n} (hr : r ∈ oddS s) :
    r.val < pivotJ s := by
  have hU := pivot_pos hs
  by_contra h
  push Not at h
  have := ne_zero_of_mem_oddSet hr
  exact this (pcol_zero_above s hU r (by simp [pidx_val]; omega))

/-- `K S' X ≈ P K S` from `S' X ≈ X S` and `K X ≈ P K`. -/
theorem combine {K X : Gen n} {SV SS P : List (Gen n)}
    (hS : Derivable (Table1 n) (FreeMonoid.ofList SV * FreeMonoid.of X)
      (FreeMonoid.of X * FreeMonoid.ofList SS))
    (hK : Derivable (Table1 n) (FreeMonoid.ofList [K, X]) (FreeMonoid.ofList (P ++ [K]))) :
    Derivable (Table1 n) (FreeMonoid.ofList (K :: SV) * FreeMonoid.of X)
      (FreeMonoid.ofList P * FreeMonoid.ofList (K :: SS)) := by
  have e1 : Derivable (Table1 n) (FreeMonoid.ofList (K :: SV) * FreeMonoid.of X)
      (FreeMonoid.ofList [K, X] * FreeMonoid.ofList SS) := by
    rw [FreeMonoid.ofList_cons]
    exact (deq (by simp only [mul_assoc])).trans
      (((Derivable.refl (FreeMonoid.of K)).mul hS).trans (deq (by simp [mul_assoc])))
  have e2 := hK.mul (Derivable.refl (FreeMonoid.ofList SS))
  exact e1.trans (e2.trans (deq (by simp [FreeMonoid.ofList_append, mul_assoc])))

/-- Subcase 1.2.3. -/
theorem squareX_pair' {s : O_ZHalf n} (hs : s ≠ 1) {x y : Fin n} (hxy : x < y)
    (hy : y.val = x.val + 1) (hle : level (sem n (Gen.x x y hxy) * s) ≤ level s)
    (hk : 0 < lde s) {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ oddS s) (hb : b ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r)
    (h1 : x ∈ [a, b, c, d] ∧ y ∈ [a, b, c, d]) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.x x y hxy) * s)) *
        FreeMonoid.of (Gen.x x y hxy)) (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  have hU := pivot_pos hs
  set σ := Equiv.swap x y with hσ
  set V := sem n (Gen.x x y hxy) * s
  have hσσ : ∀ r, σ (σ r) = r := Equiv.swap_apply_self x y
  have hcV : IsCol (gact (Gen.x x y hxy) (pcol s)) (lde s) (fun r => wint s (σ r)) :=
    isCol_x (isCol_pcol s) hxy
  obtain ⟨hpV, hcolV, hkV⟩ := state_gen hs (extent_lt_of_le hs hle) hcV hk
    (r := σ a) (by simp only [hσσ]; exact (mem_oddS_iff a).1 ha)
  have hcV' : IsCol (pcol V) (lde V) (fun r => wint s (σ r)) := by rw [hcolV, hkV]; exact hcV
  have hmemV : ∀ r, r ∈ oddS V ↔ σ r ∈ oddS s := by
    intro r; rw [oddS_eq hcV', mem_oddS_iff]; simp
  have hwV : ∀ r, wint V r = wint s (σ r) := fun r => wint_eq hcV' r
  -- `σ` maps `a, b, c, d` to themselves
  have va := Fin.lt_def.1 hab; have vb := Fin.lt_def.1 hbc; have vc := Fin.lt_def.1 hcd
  have hL : ∀ r ∈ [a, b, c, d], σ r ∈ [a, b, c, d] := by
    intro r hr
    by_cases hrx : r = x
    · rw [hrx, hσ, swap_x]; exact h1.2
    by_cases hry : r = y
    · rw [hry, hσ, swap_y]; exact h1.1
    rw [hσ, swap_o hrx hry]; exact hr
  have hmem4 : ∀ r, r ∈ [a, b, c, d] ↔ r = a ∨ r = b ∨ r = c ∨ r = d := by simp
  have hxd : x.val ≤ d.val := by
    rcases (hmem4 x).1 h1.1 with e | e | e | e <;> rw [e] <;> omega
  have hyd : y.val ≤ d.val := by
    rcases (hmem4 y).1 h1.2 with e | e | e | e <;> rw [e] <;> omega
  have hsyllV : syll V = Gen.k a b c d hab hbc hcd :: signs V [a, b, c, d] := by
    have mem' : ∀ r ∈ [a, b, c, d], r ∈ oddS V := by
      intro r hr
      rw [hmemV]
      rcases (hmem4 _).1 (hL r hr) with e | e | e | e <;> rw [e]
      exacts [ha, hb, hc, hd]
    apply syll_eq_pos V (by rw [hpV]; exact hU) (by rw [hkV]; exact hk) hab hbc hcd
      (mem' a (by simp)) (mem' b (by simp)) (mem' c (by simp)) (mem' d (by simp))
    have inj : ∀ r, (r = a ∨ r = b ∨ r = c ∨ r = d) → (r = a ∨ r = b ∨ r = c ∨ r = d ∨ d < r) := by
      intro r h
      rcases h with h | h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
        Or.inr (Or.inr (Or.inr (Or.inl h)))]
    intro r hr
    rw [hmemV] at hr
    rcases hrest _ hr with e | e | e | e | e
    · have := hL (σ r) (by rw [e]; simp); rw [hσσ] at this; exact inj r ((hmem4 r).1 this)
    · have := hL (σ r) (by rw [e]; simp); rw [hσσ] at this; exact inj r ((hmem4 r).1 this)
    · have := hL (σ r) (by rw [e]; simp); rw [hσσ] at this; exact inj r ((hmem4 r).1 this)
    · have := hL (σ r) (by rw [e]; simp); rw [hσσ] at this; exact inj r ((hmem4 r).1 this)
    · right; right; right; right
      have ve := Fin.lt_def.1 e
      have hrx : r ≠ x := fun h => by rw [h, hσ, swap_x] at ve; omega
      have hry : r ≠ y := fun h => by rw [h, hσ, swap_y] at ve; omega
      rwa [hσ, swap_o hrx hry] at e
  have hsylls : syll s = Gen.k a b c d hab hbc hcd :: signs s [a, b, c, d] :=
    syll_eq_pos s hU hk hab hbc hcd ha hb hc hd hrest
  -- the signs
  set l := [a, b, c, d]
  have hnd : l.Nodup := nd4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hperm : (l.map σ).Perm l := by
    apply List.perm_of_nodup_nodup_toFinset_eq (hnd.map σ.injective) hnd
    ext r
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r', hr', rfl⟩; exact hL r' hr'
    · intro hr; exact ⟨σ r, hL r hr, hσσ r⟩
  have hS : Derivable (Table1 n) (FreeMonoid.ofList (signs V l) * FreeMonoid.of (Gen.x x y hxy))
      (FreeMonoid.of (Gen.x x y hxy) * FreeMonoid.ofList (signs s l)) := by
    have e1 : signs V l = (l.filter fun r => tau (wint s (σ r))).map Gen.neg := by
      unfold signs; congr 1; exact List.filter_congr (fun r _ => by rw [hwV])
    have hP : (l.filter fun r => tau (wint s (σ r))).Perm
        ((l.filter fun r => tau (wint s r)).map σ) := by
      have : (l.filter fun r => tau (wint s r)).map σ =
          (l.map σ).filter fun r => tau (wint s (σ r)) := by
        rw [List.filter_map]; congr 1; apply List.filter_congr; intro r _; simp [hσσ]
      rw [this]
      exact (hperm.filter _).symm
    rw [e1]
    exact ((negs_perm hP).mul (Derivable.refl _)).trans
      (conj_swap_list hxy hy (swapOf_negs hxy _))
  -- which pair
  have hcase : (x = a ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = d) := by
    rcases (hmem4 x).1 h1.1 with ex | ex | ex | ex <;>
    rcases (hmem4 y).1 h1.2 with ey | ey | ey | ey <;>
    subst ex <;> subst ey <;> first
      | (left; exact ⟨rfl, rfl⟩) | (right; left; exact ⟨rfl, rfl⟩)
      | (right; right; exact ⟨rfl, rfl⟩) | (exfalso; omega)
  have ht := level_next_lt s hs
  have hft := (next_pos s hU hk).1
  have hdJ : d.val < pivotJ s := le_pidx_of_odd hs hd
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `{x, x+1} = {a, b}`: closed by `(−1)_[d] (−1)_[b] X_[b,d]`
    have hbd : x.val < d.val := by omega
    have hbd' : y < d := hbc.trans hcd
    refine square hs hle 1 [Gen.neg d, Gen.neg y, Gen.x y d hbd'] (Or.inl one_pos) ?_ ?_
    · rw [npath_one, hsyllV, hsylls]
      refine combine hS ?_
      exact rev_derivable (l := [Gen.x x y hab, Gen.k x y c d hab hbc hcd])
        (l' := [Gen.k x y c d hab hbc hcd, Gen.x y d hbd', Gen.neg y, Gen.neg d])
        (Derivable.of (Table1.r4a x y c d hab hbc hcd))
    · intro i hi0 hi
      have hX : level (sem n (Gen.x y d hbd') * next s) < level s :=
        level_signed_lt hs hk hft ht (by simp [Gen.tag]) (by simp [extent]; omega)
      have hfX := fixCols_gen hft (g := Gen.x y d hbd') (by simp [extent]; omega)
      simp only [List.length_cons, List.length_nil] at hi
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · have hN := level_signed_lt hs hk hfX hX (g := Gen.neg y) (by simp [Gen.tag])
          (by simp [extent]; omega)
        simpa [FreeMonoid.lift_eval_of, mul_assoc] using hN
      · simpa [FreeMonoid.lift_eval_of] using hX
  · -- `{x, x+1} = {b, c}`: closed by `X_[b,c]`
    refine square_short hs hle [Gen.x x y hbc] (by simp) ?_
    rw [hsyllV, hsylls]
    exact combine hS (ksym2 hab hbc hcd).symm
  · -- `{x, x+1} = {c, d}`: closed by `X_[b,d]`
    have hbd : b < y := hbc.trans hcd
    refine square_short hs hle [Gen.x b y hbd] (by simp) ?_
    rw [hsyllV, hsylls]
    refine combine hS ?_
    exact rev_derivable (l := [Gen.x x y hcd, Gen.k a b x y hab hbc hcd])
      (l' := [Gen.k a b x y hab hbc hcd, Gen.x b y hbd])
      (Derivable.of (Table1.r4c a b x y hab hbc hcd))

end QCert.LiRossSelinger
