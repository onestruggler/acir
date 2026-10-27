/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Main Cases 1 and 2, and the Main Lemma

`G = X_[0,x]` below the pivot at a positive exponent.  The paper's case
analysis (Main Cases 1, 2) is not correct as written (see the README); here
the square is closed by *pair confluence*: the first syllable of `s` reduces
a matched pair `A` of the pivot column, the first syllable of `X_[0,x] s`
reduces (up to the permutation) a matched pair `B`, and the two reductions
are joined below the level of `s`.
-/
import QCert.HadamardPi.Confluence

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}


/-! ### Monomial letters -/

/-- `X` and `(-1)` letters, which only permute and negate entries. -/
def IsMono : Gen n → Prop
  | .H _ _ _ => False
  | _ => True

/-- A path of monomial letters whose indices have `(q+1, 0, 0)` below `L`,
from a state below `L`, stays below `L`. -/
theorem mono_path {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, IsMono g ∧ ∀ i ∈ g.idx, lev0 i < L) →
      lev t < L → PathLt L w t
  | [], _, _, h => h
  | g :: w, t, hw, h => by
    have hw' := mono_path w t (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')) h
    refine ⟨hw', ?_⟩
    obtain ⟨hm, hi⟩ := hw g List.mem_cons_self
    rw [run_cons]
    cases g with
    | Z p =>
      exact lt_of_le_of_lt lev_Z_le_max (max_lt hw'.last (hi p (by simp [Gen.idx])))
    | X p q hpq =>
      exact lt_of_le_of_lt (lev_X_le_max hpq) (max_lt hw'.last (hi q (by simp [Gen.idx])))
    | H p q _ => exact absurd hm id

/-! ### Small derivations, moved to any increasing indices -/

theorem smono2 {a b : Fin n} (h : a < b) : StrictMono ![a, b] := by
  rw [Fin.strictMono_iff_lt_succ]; intro i; fin_cases i; simpa using h

theorem smono3 {a b c : Fin n} (h1 : a < b) (h2 : b < c) : StrictMono ![a, b, c] := by
  rw [Fin.strictMono_iff_lt_succ]; intro i; fin_cases i
  · simpa using h1
  · simpa using h2

/-- `H_[p,q] X_[0,x] ≈ X_[0,x] Y H_B` with `B` the image of `(p,q)` under the
transposition of `0` and `x`, and `Y` a monomial word. -/
theorem conj_HX {z x p q : Fin n} (hz : (z : ℕ) = 0) (hzx : z < x) (hpq : p < q) :
    ∃ (b1 b2 : Fin n) (hb : b1 < b2) (Y : List (Gen n)),
      ((b1 = Equiv.swap z x p ∧ b2 = Equiv.swap z x q) ∨
        (b1 = Equiv.swap z x q ∧ b2 = Equiv.swap z x p)) ∧
      (∀ g ∈ Y, IsMono g ∧ ∀ i ∈ g.idx, i = z ∨ i = x ∨ i = p ∨ i = q) ∧
      Derivable Fig6 (ofList [Gen.H p q hpq, Gen.X z x hzx])
        (ofList ([Gen.X z x hzx] ++ Y ++ [Gen.H b1 b2 hb])) := by
  have hz0 : ∀ i : Fin n, z ≤ i := fun i => Fin.le_def.2 (by omega)
  by_cases hpz : p = z
  · subst hpz
    by_cases hqx : q = x
    · -- (0, x) ↦ (x, 0): `H_[0,x] X_[0,x] ≈ X_[0,x] (-1)_[0] X_[0,x] H_[0,x]`
      subst hqx
      refine ⟨p, q, hpq, [Gen.Z p, Gen.X p q hpq], Or.inr ⟨by simp, by simp⟩, ?_, ?_⟩
      · intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp [IsMono, Gen.idx]
      · exact der_map ![p, q] (smono2 hpq) (L := [hL 0 1, xL 0 1])
          (R := [xL 0 1, zL 0, xL 0 1, hL 0 1])
          (derive_of [.rel .d2 [0, 1] 0 false, .rel .a2 [0, 1] 0 false, .rel .c1 [0, 1] 1 false]
            (by decide +kernel))
    rcases lt_or_gt_of_ne hqx with hqx' | hqx'
    · -- `q < x`: `(0, q) ↦ (x, q)`, reversed
      refine ⟨q, x, hqx', [Gen.Z q, Gen.X q x hqx'], Or.inr ⟨by
        rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt hpq) hqx], by simp⟩, ?_, ?_⟩
      · intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp [IsMono, Gen.idx]
      · exact der_map ![p, q, x] (smono3 hpq hqx') (L := [hL 0 1, xL 0 2])
          (R := [xL 0 2, zL 1, xL 1 2, hL 1 2])
          (derive_of [.rel .a2 [1, 2] 2 false, .rel .c3 [0, 1, 2] 1 true,
            .rel .a2 [1, 2] 0 false, .rel .c5 [0, 1, 2] 1 false, .rel .a2 [1, 2] 2 true,
            .rel .a2 [0, 1] 1 false, .rel .c4 [0, 1, 2] 2 false, .rel .a2 [0, 1] 3 true,
            .rel .d2 [1, 2] 2 false, .rel .c3 [0, 1, 2] 0 false, .rel .c1 [1, 2] 1 false]
            (by decide +kernel))
    · -- `x < q`: `(0, q) ↦ (x, q)`
      refine ⟨x, q, hqx', [], Or.inl ⟨by simp, by
        rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt hpq) (ne_of_gt hqx')]⟩, by simp, ?_⟩
      exact der_map ![p, x, q] (smono3 hzx hqx') (L := [hL 0 2, xL 0 1]) (R := [xL 0 1, hL 1 2])
        (derive_of [.rel .a2 [0, 1] 0 false, .rel .c4 [0, 1, 2] 1 false, .rel .a2 [0, 1] 2 true]
          (by decide +kernel))
  have hzp : z < p := lt_of_le_of_ne (hz0 p) (Ne.symm hpz)
  by_cases hqx : q = x
  · -- `0 < p < x = q`: `(p, x) ↦ (p, 0)`, reversed
    subst hqx
    refine ⟨z, p, hzp, [Gen.Z z, Gen.X z p hzp], Or.inr ⟨by simp, by
      rw [Equiv.swap_apply_of_ne_of_ne hpz (ne_of_lt hpq)]⟩, ?_, ?_⟩
    · intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp [IsMono, Gen.idx]
    · exact der_map ![z, p, q] (smono3 hzp hpq) (L := [hL 1 2, xL 0 2])
        (R := [xL 0 2, zL 0, xL 0 1, hL 0 1])
        (derive_of [.rel .a2 [0, 1] 1 false, .rel .c2 [0, 1, 2] 2 false, .rel .c4 [0, 1, 2] 0 true,
          .rel .c5 [0, 1, 2] 1 true, .rel .d2 [0, 1] 2 false, .rel .a2 [0, 1] 2 false,
          .rel .c2 [0, 1, 2] 1 true, .rel .a2 [0, 1] 0 true, .rel .c1 [0, 1] 1 false]
          (by decide +kernel))
  by_cases hpx : p = x
  · -- `p = x < q`: `(x, q) ↦ (0, q)`
    subst hpx
    refine ⟨z, q, lt_trans hzp hpq, [], Or.inl ⟨by simp, by
      rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt (lt_trans hzp hpq)) hqx]⟩, by simp, ?_⟩
    exact Derivable.of (Fig6.c4 hzp hpq)
  · -- `p`, `q` away from `0`, `x`
    have hqz : q ≠ z := ne_of_gt (lt_trans hzp hpq)
    refine ⟨p, q, hpq, [], Or.inl ⟨by rw [Equiv.swap_apply_of_ne_of_ne hpz hpx],
      by rw [Equiv.swap_apply_of_ne_of_ne hqz hqx]⟩, by simp, ?_⟩
    exact (rl_b5 hzx hpq (Ne.symm hpz) (Ne.symm hqz) (Ne.symm hpx) (Ne.symm hqx)).symm

/-- The first syllable `H_[0,i₂] X_[0,i₁]` (or `H_[0,i₂]` when `i₁ = 0`) is
`X₁ H_[i₁,i₂]` with `X₁ = X_[0,i₁]` (or `ε`). -/
theorem syl_split {s : O n} {i1 i2 z : Fin n} (hz2 : z < i2) (hz1le : z ≤ i1) (h12 : i1 < i2)
    (hsyl : syl s = FreeMonoid.of (Gen.H z i2 hz2) *
      (if hz1 : z < i1 then FreeMonoid.of (Gen.X z i1 hz1) else 1)) :
    ∃ X1 : List (Gen n), Derivable Fig6 (syl s) (ofList (X1 ++ [Gen.H i1 i2 h12])) ∧
      (∀ g ∈ X1, IsMono g ∧ ∀ i ∈ g.idx, i = z ∨ i = i1) ∧
      Derivable Fig6 (ofList (X1 ++ X1)) 1 ∧ ∀ u : O n, run X1 (run X1 u) = u := by
  by_cases hz1 : z < i1
  · refine ⟨[Gen.X z i1 hz1], ?_, ?_, rl_a2 hz1, fun u => by
      rw [run_cons, run_nil, run_cons, run_nil, sem_sq_assoc]⟩
    · rw [hsyl, dif_pos hz1]
      exact rl_HX hz1 h12
    · intro g hg; simp at hg; subst hg; simp [IsMono, Gen.idx]
  · have e : i1 = z := le_antisymm (not_lt.1 hz1) hz1le
    subst e
    refine ⟨[], ?_, by simp, Derivable.refl _, fun u => by simp⟩
    rw [hsyl, dif_neg hz1, mul_one]
    exact Derivable.refl _


theorem der_mid (L M R M' : List (Gen n)) (h : Derivable Fig6 (ofList M) (ofList M')) :
    Derivable Fig6 (ofList (L ++ M ++ R)) (ofList (L ++ M' ++ R)) := by
  simp only [ofList_append]
  exact ((Derivable.refl _).mul h).mul (Derivable.refl _)

theorem der_eq {L R L' R' : List (Gen n)} (h : Derivable Fig6 (ofList L) (ofList R))
    (hL : L = L') (hR : R = R') : Derivable Fig6 (ofList L') (ofList R') := by
  subst hL hR; exact h

/-- Main Cases 1 and 2: `G = X_[0,x]` below the pivot, at a positive
exponent. -/
theorem main_X_odd {s : O n} (hs : s ≠ 1) {z x : Fin n} (hzx : z < x) (hz : (z : ℕ) = 0)
    (hr : sem n (Gen.X z x hzx) * s ≠ 1) (hxJ : (x : ℕ) < piv s)
    (hk : lde (col s (pj s (piv_pos hs))) ≠ 0) : MainSquare s (Gen.X z x hzx) := by
  classical
  have hp := piv_pos hs
  set v := col s (pj s (piv_pos hs)) with hvdef
  have hR : InRing v := col_inRing s _
  have hzJ : (z : ℕ) < piv s := lt_trans (Fin.lt_def.1 hzx) hxJ
  have hidx : ∀ i ∈ (Gen.X z x hzx).idx, (i : ℕ) < piv s := by
    intro i hi; simp [Gen.idx] at hi; rcases hi with rfl | rfl
    · exact hzJ
    · exact hxJ
  -- the pivot column of `r = G s` is the column of `s` with entries `0`, `x` exchanged
  have hpiv : piv (sem n (Gen.X z x hzx) * s) = piv s := piv_eq_of_col hp hidx (fun h => hk (by
      rw [← lde_xv z x hR, show xv z x v = gv (Gen.X z x hzx) v from rfl, h]
      exact lde_single (Or.inl rfl)))
  have hcolr : col (sem n (Gen.X z x hzx) * s) (pj _ (piv_pos hr)) = xv z x v := by
    have : pj _ (piv_pos hr) = pj s hp := Fin.ext (by simp only [pj]; rw [hpiv])
    rw [this, col_sem_mul]; rfl
  have hkr : lde (col (sem n (Gen.X z x hzx) * s) (pj _ (piv_pos hr))) ≠ 0 := by
    rw [hcolr, lde_xv z x hR]; exact hk
  have hnumr : ∀ i, num (col (sem n (Gen.X z x hzx) * s) (pj _ (piv_pos hr))) i =
      num v (Equiv.swap z x i) := by
    intro i; rw [hcolr, num_xv z x hR]
  have hσJ : ∀ i : Fin n, (i : ℕ) < piv s → (Equiv.swap z x i : ℕ) < piv s := by
    intro i hi
    rcases eq_or_ne i z with rfl | h1
    · rw [Equiv.swap_apply_left]; exact hxJ
    rcases eq_or_ne i x with rfl | h2
    · rw [Equiv.swap_apply_right]; exact hzJ
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hi
  -- the matched pair `A` of `s` and the first syllable `N ≈ X₁ H_A`
  obtain ⟨i1, i2, z1, hz2, hz1, hz1le, h12, hi1J, hi2J, -, hsame, -, -, hsyl⟩ :=
    syl_pos_form hs hk
  obtain ⟨X1, hN, hX1, hX1X1, hX1inv⟩ := syl_split hz2 hz1le h12 hsyl
  -- the matched pair `A'` of `r` and its first syllable `N' ≈ X₁' H_A'`
  obtain ⟨i1', i2', z2, hz2', hz2'', hz2le, h12', hi1J', hi2J', -, hsame', -, -, hsyl'⟩ :=
    syl_pos_form hr hkr
  obtain ⟨X1', hN', hX1', -, -⟩ := syl_split hz2' hz2le h12' hsyl'
  rw [hpiv] at hi1J' hi2J'
  -- `H_A' G ≈ G Y H_B`, with `B` the image of `A'`, a matched pair of `s`
  obtain ⟨b1, b2, hb, Y, hBimg, hY, hconj⟩ := conj_HX hz hzx h12'
  have hsameB : SameOdd (num v (Equiv.swap z x i1')) (num v (Equiv.swap z x i2')) := by
    rw [← hnumr, ← hnumr]; exact hsame'
  have hB : SameOdd (num v b1) (num v b2) := by
    rcases hBimg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsameB
    · exact hsameB.symm
  have hb2J : (b2 : ℕ) < piv s := by
    rcases hBimg with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hσJ _ hi2J'
    · exact hσJ _ hi1J'
  -- `D H_A ≈ H_B` below `s`
  obtain ⟨D, hD, hPD⟩ := pair_confluence hs hk h12 hb hi2J hb2J hsame hB
  -- the square: `N' G ≈ (X₁' G Y D X₁) N`
  have step1 : Derivable Fig6 (syl (sem n (Gen.X z x hzx) * s) * FreeMonoid.of (Gen.X z x hzx))
      (ofList (X1' ++ [Gen.H i1' i2' h12', Gen.X z x hzx])) := by
    have := hN'.mul (Derivable.refl (FreeMonoid.of (Gen.X z x hzx)))
    rwa [← ofList_singleton, ← ofList_append, List.append_assoc, List.singleton_append] at this
  have step2 := der_mid X1' [Gen.H i1' i2' h12', Gen.X z x hzx] []
    ([Gen.X z x hzx] ++ Y ++ [Gen.H b1 b2 hb]) hconj
  have step3 := der_mid (X1' ++ [Gen.X z x hzx] ++ Y) [Gen.H b1 b2 hb] []
    (D ++ [Gen.H i1 i2 h12]) hD.symm
  have step4 := der_mid (X1' ++ [Gen.X z x hzx] ++ Y ++ D) [] [Gen.H i1 i2 h12] (X1 ++ X1)
    (by simpa using hX1X1.symm)
  have step5 : Derivable Fig6
      (ofList (X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ (X1 ++ X1) ++ [Gen.H i1 i2 h12]))
      (ofList (X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ X1) * syl s) := by
    have := (Derivable.refl (ofList (X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ X1))).mul hN.symm
    rw [← ofList_append] at this
    exact der_eq (R := X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ X1 ++ (X1 ++ [Gen.H i1 i2 h12]))
      (Derivable.refl _) (by simp) rfl |>.trans this
  have hder : Derivable Fig6 (syl (sem n (Gen.X z x hzx) * s) * FreeMonoid.of (Gen.X z x hzx))
      (ofList (X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ X1) * syl s) := by
    refine step1.trans ?_
    refine (der_eq step2 (by simp) rfl).trans ?_
    refine (der_eq step3 (by simp) rfl).trans ?_
    refine (der_eq step4 (by simp) rfl).trans ?_
    exact step5
  -- the path `X₁' G Y D X₁` from `t = N s` stays below `s`
  have ht : FreeMonoid.lift (sem n) (syl s) * s = run (X1 ++ [Gen.H i1 i2 h12]) s := by
    rw [run_eq_lift, derivable_sound fig6_sound hN]
  have hA_s : run X1 (run (X1 ++ [Gen.H i1 i2 h12]) s) = run [Gen.H i1 i2 h12] s := by
    rw [run_append, hX1inv]
  have hlev0 : ∀ i : Fin n, (i : ℕ) < piv s → lev0 i < lev s := fun i hi => lev0_lt_of_lde hp hi hk
  have hi1J0 : (i1 : ℕ) < piv s := hi1J
  have hz1J : (z1 : ℕ) < piv s := by omega
  have hz2J : (z2 : ℕ) < piv s := by omega
  have hpath : PathLt (lev s) (X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ X1)
      (FreeMonoid.lift (sem n) (syl s) * s) := by
    rw [ht, show X1' ++ [Gen.X z x hzx] ++ Y ++ D ++ X1 =
      (X1' ++ [Gen.X z x hzx] ++ Y) ++ (D ++ X1) by simp]
    refine (PathLt.append _ _ _).2 ⟨(PathLt.append _ _ _).2 ⟨?_, ?_⟩, ?_⟩
    · apply mono_path X1 _ _ (by rw [← ht]; exact lev_syl_lt hs)
      intro g hg
      obtain ⟨hm, hi⟩ := hX1 g hg
      refine ⟨hm, fun i hi' => hlev0 i ?_⟩
      rcases hi i hi' with rfl | rfl
      · exact hz1J
      · exact hi1J0
    · rw [hA_s]; exact hPD
    · apply mono_path
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with (hg | rfl) | hg
        · obtain ⟨hm, hi⟩ := hX1' g hg
          refine ⟨hm, fun i hi' => hlev0 i ?_⟩
          rcases hi i hi' with rfl | rfl
          · exact hz2J
          · exact hi1J'
        · refine ⟨trivial, fun i hi' => hlev0 i (hidx i hi')⟩
        · obtain ⟨hm, hi⟩ := hY g hg
          refine ⟨hm, fun i hi' => hlev0 i ?_⟩
          rcases hi i hi' with rfl | rfl | rfl | rfl
          · exact hzJ
          · exact hxJ
          · exact hi1J'
          · exact hi2J'
      · rw [run_append, hA_s, ← run_append, run_eq_of_der hD, run_cons, run_nil]
        exact lev_pair_lt hp hb hb2J hk hB
  exact square_of hs hr _ hpath hder

/-- Lemma A.7 (Main Lemma), for every basic generator; the cases at a
positive exponent with `X_[0,x]` or `H_[0,1]` below the pivot (Main Cases
1, 2, 9, 10) are `main_X_odd` and `main_H_odd`. -/
theorem main_lemma (s : O n) (hs : s ≠ 1) (g : Gen n) (hg : Basic g) : MainSquare s g := by
  by_cases hr : sem n g * s = 1
  · have hsg : s = sem n g := by
      have := congrArg (sem n g * ·) hr
      simp only [sem_sq_assoc, mul_one] at this
      exact this
    subst hsg
    exact square_pro hs (syl_basic g hg)
  cases g with
  | Z a =>
    simp only [Basic] at hg
    obtain ⟨a, ha⟩ := a
    simp only at hg
    subst hg
    exact main_Z hs ha hr
  | X a x h =>
    simp only [Basic] at hg
    exact main_X hs h hg hr (main_X_odd hs h hg hr)
  | H a b h =>
    simp only [Basic] at hg
    exact main_H hs h hg.1 hg.2 hr

end QCert.HadamardPi
