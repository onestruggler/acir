/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Theorem 4.14: completeness, from the Main Lemma

The argument of Appendix A (after Greylyn, Lemmas 32 and 33):

* `StepAt M g` says that the square at the state `M` and the generator
  `g` closes: `nw (⟦g⟧ M) · g ≈ nw M`.
* Lemma A.6: every generator is a word of basic generators
  (`X_[0,x]`, `(-1)_[0]`, `H_[0,1]`, the paper's `X_[1,x]`, `(-1)_[1]`,
  `H_[1,2]`) whose path from any state stays at or below the levels of its
  two ends (`bw`, `bw_deriv`, `bw_path`).
* Lemma A.7, the Main Lemma (`main_lemma`): for a basic generator `g` at a
  state `s ≠ I` with first syllable `N : s ⇒ t`, there are normal syllables
  `N'` from `⟦g⟧ s` to a state `q` and a path `G'` from `t` to `q`, all of
  whose states lie strictly below `s`, with `N' g ≈ G' N`.
* Lemma A.8, by induction on the level: the square closes at every state
  and basic generator (`basic_step`); with Lemma A.6, at every generator
  (`step_all`).  Lemma A.9 and Theorem 4.14 are then
  `QCert.NormalWords.isPresentationOf`.
-/
import QCert.HadamardPi.Levels
import QCert.HadamardPi.Derive

namespace QCert.HadamardPi

open Matrix Finset

variable {n : ℕ}

/-- The square at the state `M` and the generator `g` closes. -/
def StepAt (M : O n) (g : Gen n) : Prop :=
  Derivable Fig6 (nw (sem n g * M) * FreeMonoid.of g) (nw M)

/-- The state reached from `t` by the word `w`. -/
noncomputable def run (w : List (Gen n)) (t : O n) : O n :=
  FreeMonoid.lift (sem n) (FreeMonoid.ofList w) * t

@[simp] theorem run_nil (t : O n) : run [] t = t := by simp [run]

theorem run_cons (g : Gen n) (w : List (Gen n)) (t : O n) :
    run (g :: w) t = sem n g * run w t := by
  simp [run, FreeMonoid.ofList_cons, mul_assoc]

/-- Every state visited by the word `w` from `t` (the rightmost letter
acting first), `t` and the last one included, is strictly below `L`. -/
def PathLt (L : ℕ ×ₗ (ℕ ×ₗ ℕ)) : List (Gen n) → O n → Prop
  | [], t => lev t < L
  | g :: w, t => PathLt L w t ∧ lev (run (g :: w) t) < L

theorem PathLt.last {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ {w : List (Gen n)} {t : O n}, PathLt L w t → lev (run w t) < L
  | [], _, h => by simpa using h
  | _ :: _, _, h => h.2

/-- A path whose every edge closes its square closes its square. -/
theorem path_step {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} (P : Gen n → Prop)
    (IH : ∀ t g, P g → lev t < L → lev (sem n g * t) < L → StepAt t g) :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, P g) → PathLt L w t →
      Derivable Fig6 (nw (run w t) * FreeMonoid.ofList w) (nw t)
  | [], t, _, _ => by simpa using Derivable.refl (nw t)
  | g :: w, t, hP, h => by
    have hw := path_step P IH w t (fun g' hg' => hP g' (List.mem_cons_of_mem _ hg')) h.1
    have hg := IH (run w t) g (hP g List.mem_cons_self) h.1.last (by rw [← run_cons]; exact h.2)
    rw [run_cons, FreeMonoid.ofList_cons, ← mul_assoc]
    exact (hg.mul (Derivable.refl _)).trans hw

/-- A path of generators whose every square closes, without levels. -/
theorem path_step' (P : Gen n → Prop) (IH : ∀ t g, P g → StepAt t g) :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, P g) →
      Derivable Fig6 (nw (run w t) * FreeMonoid.ofList w) (nw t)
  | [], t, _ => by simpa using Derivable.refl (nw t)
  | g :: w, t, hP => by
    rw [run_cons, FreeMonoid.ofList_cons, ← mul_assoc]
    exact ((IH (run w t) g (hP g List.mem_cons_self)).mul (Derivable.refl _)).trans
      (path_step' P IH w t fun g' hg' => hP g' (List.mem_cons_of_mem _ hg'))

/-! ### Basic generators and Lemma A.6 -/

/-- The basic generators `X_[0,x]`, `(-1)_[0]`, `H_[0,1]` (the paper's
`X_[1,x]`, `(-1)_[1]`, `H_[1,2]`). -/
def Basic : Gen n → Prop
  | .Z a => (a : ℕ) = 0
  | .X a _ _ => (a : ℕ) = 0
  | .H a b _ => (a : ℕ) = 0 ∧ (b : ℕ) = 1

/-- The basic word of `H_[0,c]`: `X_[0,1] X_[0,c] X_[0,1] H_[0,1] X_[0,1] X_[0,c] X_[0,1]`
for `c > 1`. -/
def bwH0 (c : Fin n) (hc : 0 < (c : ℕ)) : List (Gen n) :=
  if hc1 : 1 < (c : ℕ) then
    [.X ⟨0, by omega⟩ ⟨1, hc1.trans c.2⟩ (by simp [Fin.lt_def]),
      .X ⟨0, by omega⟩ c (by simp [Fin.lt_def]; omega),
      .X ⟨0, by omega⟩ ⟨1, hc1.trans c.2⟩ (by simp [Fin.lt_def]),
      .H ⟨0, by omega⟩ ⟨1, hc1.trans c.2⟩ (by simp [Fin.lt_def]),
      .X ⟨0, by omega⟩ ⟨1, hc1.trans c.2⟩ (by simp [Fin.lt_def]),
      .X ⟨0, by omega⟩ c (by simp [Fin.lt_def]; omega),
      .X ⟨0, by omega⟩ ⟨1, hc1.trans c.2⟩ (by simp [Fin.lt_def])]
  else [.H ⟨0, by omega⟩ c (by simp [Fin.lt_def]; omega)]

/-- A word of basic generators equal to a generator (Lemma A.6):
`(-1)_[a] = X_[0,a] (-1)_[0] X_[0,a]`, `X_[b,c] = X_[0,b] X_[0,c] X_[0,b]`,
`H_[0,c] = X_[0,1] X_[0,c] X_[0,1] H_[0,1] X_[0,1] X_[0,c] X_[0,1]` and
`H_[b,c] = X_[0,b] H_[0,c] X_[0,b]`. -/
def bw : Gen n → List (Gen n)
  | .Z a =>
    if h : 0 < (a : ℕ) then
      [.X ⟨0, by omega⟩ a h, .Z ⟨0, by omega⟩, .X ⟨0, by omega⟩ a h]
    else [.Z a]
  | .X b c hbc =>
    if h : 0 < (b : ℕ) then
      [.X ⟨0, by omega⟩ b h, .X ⟨0, by omega⟩ c (by rw [Fin.lt_def] at hbc ⊢; simp; omega),
        .X ⟨0, by omega⟩ b h]
    else [.X b c hbc]
  | .H b c hbc =>
    if h : 0 < (b : ℕ) then
      .X ⟨0, by omega⟩ b h :: bwH0 c (by rw [Fin.lt_def] at hbc; omega) ++ [.X ⟨0, by omega⟩ b h]
    else bwH0 c (by rw [Fin.lt_def] at hbc; omega)

theorem der_bwH0 (c : Fin n) (hc : 0 < (c : ℕ)) :
    Derivable Fig6 (FreeMonoid.of (Gen.H ⟨0, by omega⟩ c (by simp [Fin.lt_def]; omega)))
      (FreeMonoid.ofList (bwH0 c hc)) := by
  unfold bwH0
  split_ifs with hc1
  · set z : Fin n := ⟨0, by omega⟩
    set o : Fin n := ⟨1, hc1.trans c.2⟩
    have hzo : z < o := by simp [z, o, Fin.lt_def]
    have hoc : o < c := by simp [o, Fin.lt_def]; omega
    -- `X_[0,1] X_[0,c] X_[0,1] ≈ X_[1,c]` by (c2)
    have h1 : Derivable Fig6 (X_[z,o] * X_[z,c] * X_[z,o]) X_[o,c] :=
      conj_r (Derivable.of (Fig6.c2 hzo hoc)) (Derivable.of (Fig6.a2 hzo))
    -- `X_[1,c] H_[0,1] X_[1,c] ≈ H_[0,c]` by (c5)
    have h2 : Derivable Fig6 (X_[o,c] * H_[z,o] * X_[o,c]) H_[z,c] :=
      conj_r (Derivable.of (Fig6.c5 hzo hoc)) (Derivable.of (Fig6.a2 hoc))
    exact h2.symm.trans ((h1.symm.mul (Derivable.refl _)).mul h1.symm)
  · exact Derivable.refl _

/-- Lemma A.6, the equation: a generator is equal to its basic word. -/
theorem bw_deriv (g : Gen n) : Derivable Fig6 (FreeMonoid.of g) (FreeMonoid.ofList (bw g)) := by
  cases g with
  | Z a =>
    simp only [bw]
    split_ifs with h
    · exact (conj_l (Derivable.of (Fig6.c1 (a := ⟨0, by omega⟩) (b := a) h))
        (Derivable.of (Fig6.a2 (a := ⟨0, by omega⟩) (b := a) h))).symm
    · exact Derivable.refl _
  | X b c hbc =>
    simp only [bw]
    split_ifs with h
    · exact (conj_r (Derivable.of (Fig6.c2 (a := ⟨0, by omega⟩) (b := b) (c := c) h hbc))
        (Derivable.of (Fig6.a2 (a := ⟨0, by omega⟩) (b := b) h))).symm
    · exact Derivable.refl _
  | H b c hbc =>
    simp only [bw]
    split_ifs with h
    · have hc : 0 < (c : ℕ) := by rw [Fin.lt_def] at hbc; omega
      -- `X_[0,b] H_[0,c] X_[0,b] ≈ H_[b,c]` by (c4)
      have h4 := conj_r (Derivable.of (Fig6.c4 (a := ⟨0, by omega⟩) (b := b) (c := c) h hbc))
        (Derivable.of (Fig6.a2 (a := ⟨0, by omega⟩) (b := b) h))
      exact h4.symm.trans (((Derivable.refl _).mul (der_bwH0 c hc)).mul (Derivable.refl _))
    · obtain ⟨bv, hbv⟩ := b
      simp only at h
      obtain rfl : bv = 0 := by omega
      exact der_bwH0 c _

theorem bwH0_basic (c : Fin n) (hc : 0 < (c : ℕ)) : ∀ g' ∈ bwH0 c hc, Basic g' := by
  unfold bwH0
  split_ifs with hc1
  · intro g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with h | h | h | h | h | h | h <;> subst h <;> simp [Basic]
  · intro g' hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    subst hg'; simp [Basic]; omega

theorem bw_basic (g : Gen n) : ∀ g' ∈ bw g, Basic g' := by
  cases g with
  | Z a =>
    simp only [bw]; split_ifs with h <;> intro g' hg' <;> simp at hg' <;>
      rcases hg' with rfl | rfl | rfl <;> simp [Basic] <;> omega
  | X b c hbc =>
    simp only [bw]; split_ifs with h <;> intro g' hg' <;> simp at hg' <;>
      rcases hg' with rfl | rfl | rfl <;> simp [Basic] <;> omega
  | H b c hbc =>
    simp only [bw]; split_ifs with h
    · intro g' hg'
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hg'
      rcases hg' with rfl | hg' | rfl
      · simp [Basic]
      · exact bwH0_basic c _ g' hg'
      · simp [Basic]
    · exact bwH0_basic c _

theorem run_bw (g : Gen n) (t : O n) : run (bw g) t = sem n g * t := by
  rw [run, ← derivable_sound fig6_sound (bw_deriv g), FreeMonoid.lift_eval_of]

theorem sem_sq (g : Gen n) : sem n g * sem n g = 1 := by
  have h : Fig6 (FreeMonoid.of g * FreeMonoid.of g) 1 := by
    cases g with
    | Z a => exact Fig6.a1 a
    | X a b h => exact Fig6.a2 h
    | H a b h => exact Fig6.a3 h
  simpa using fig6_sound h

theorem sem_sq_assoc (g : Gen n) (x : O n) : sem n g * (sem n g * x) = x := by
  rw [← mul_assoc, sem_sq, one_mul]

theorem run_append (w w' : List (Gen n)) (t : O n) : run (w ++ w') t = run w (run w' t) := by
  simp [run, FreeMonoid.ofList_append, mul_assoc]

/-- Every generator is an involution, so a word followed by its reverse
cancels. -/
theorem run_reverse_run (w : List (Gen n)) (t : O n) : run w.reverse (run w t) = t := by
  induction w generalizing t with
  | nil => simp
  | cons g w ih =>
    rw [List.reverse_cons, run_append, run_cons, run_cons, run_nil, sem_sq_assoc, ih]

theorem PathLt.append {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ (w w' : List (Gen n)) (t : O n),
      PathLt L (w ++ w') t ↔ PathLt L w' t ∧ PathLt L w (run w' t)
  | [], w', t => by
    simp only [List.nil_append, PathLt]
    exact ⟨fun h => ⟨h, h.last⟩, fun h => h.1⟩
  | g :: w, w', t => by
    simp only [List.cons_append, PathLt]
    rw [PathLt.append w w' t, ← List.cons_append, run_append]
    tauto

/-- The level `(q+1, 0, 0)` grows with `q`. -/
theorem lev0_mono {q q' : ℕ} (h : q ≤ q') : lev0 q ≤ lev0 q' := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega)))
  · exact le_rfl

/-- An `X` letter whose target `q` has `(q+1, 0, 0)` below `L`. -/
def XLt (L : ℕ ×ₗ (ℕ ×ₗ ℕ)) (g : Gen n) : Prop :=
  ∃ p q : Fin n, ∃ h : p < q, g = Gen.X p q h ∧ lev0 q < L

/-- A path of such `X` letters from a state below `L` stays below `L`. -/
theorem xs_path {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, XLt L g) → lev t < L → PathLt L w t
  | [], _, _, h => h
  | g :: w, t, hX, h => by
    have hw := xs_path w t (fun g' hg' => hX g' (List.mem_cons_of_mem _ hg')) h
    refine ⟨hw, ?_⟩
    obtain ⟨p, q, hpq, rfl, hq⟩ := hX g List.mem_cons_self
    rw [run_cons]
    exact lt_of_le_of_lt (lev_X_le_max hpq) (max_lt hw.last hq)

/-- A palindrome `P m Pʳ` of `X` letters around one letter `m` stays below
any bound on its two ends. -/
theorem palin_path {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} {t : O n} (P : List (Gen n)) (m : Gen n)
    (hX : ∀ g ∈ P, XLt L g) (h1 : lev t < L) (h2 : lev (run (P ++ m :: P.reverse) t) < L) :
    PathLt L (P ++ m :: P.reverse) t := by
  have hXr : ∀ g ∈ P.reverse, XLt L g := fun g hg => hX g (List.mem_reverse.1 hg)
  rw [PathLt.append]
  have hr : run (P ++ m :: P.reverse) t = run P (run (m :: P.reverse) t) := run_append _ _ _
  have h5 : lev (run (m :: P.reverse) t) < L := by
    have := (xs_path P.reverse (run P (run (m :: P.reverse) t)) hXr (hr ▸ h2)).last
    rwa [run_reverse_run] at this
  exact ⟨⟨xs_path _ t hXr h1, h5⟩, xs_path P _ hX h5⟩

theorem lev0_le_H {q c : ℕ} (hq : q ≤ c) : lev0 q ≤ toLex (c + 1, toLex (1, 2)) := by
  rcases lt_or_eq_of_le hq with h | rfl
  · exact le_of_lt (Prod.Lex.toLex_lt_toLex.2 (Or.inl (by omega)))
  · exact le_of_lt (Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl,
      Prod.Lex.toLex_lt_toLex.2 (Or.inl zero_lt_one)⟩))

/-- Lemma A.6, the levels: the path of the basic word stays below any
bound on the levels of its two ends. -/
theorem bw_path (t : O n) (g : Gen n) {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} (h1 : lev t < L)
    (h2 : lev (sem n g * t) < L) : PathLt L (bw g) t := by
  have hr : run (bw g) t = sem n g * t := run_bw g t
  -- `(q+1, 0, 0)` is below `L` for every index up to the largest index of `g`
  have hlev0 : ∀ (top : ℕ), (piv t ≤ top → lev0 top ≤ lev (sem n g * t)) →
      ∀ q ≤ top, lev0 q < L := by
    intro top htop q hq
    rcases Nat.lt_or_ge q (piv t) with h | h
    · exact lt_of_le_of_lt (lev0_le h) h1
    · exact lt_of_le_of_lt ((lev0_mono hq).trans (htop (by omega))) h2
  have hXlt : ∀ (top : ℕ), (∀ q ≤ top, lev0 q < L) → ∀ (p q : Fin n) (h : p < q),
      (q : ℕ) ≤ top → XLt L (Gen.X p q h) := fun top htop p q h hq => ⟨p, q, h, rfl, htop q hq⟩
  rw [← hr] at h2
  cases g with
  | Z a =>
    have hb := hlev0 a (fun h => (lev_Z_of_le h).ge)
    revert h2
    simp only [bw]
    split_ifs with ha
    · intro h2
      exact palin_path [Gen.X ⟨0, by omega⟩ a ha] (Gen.Z ⟨0, by omega⟩)
        (by simp only [List.mem_singleton, forall_eq]; exact hXlt a hb _ _ _ le_rfl) h1 h2
    · intro h2; exact ⟨h1, h2⟩
  | X b c hbc =>
    have hb := hlev0 c (fun h => (lev_X_of_le hbc h).ge)
    revert h2
    simp only [bw]
    split_ifs with h0
    · intro h2
      exact palin_path [Gen.X ⟨0, by omega⟩ b h0] (Gen.X ⟨0, by omega⟩ c _)
        (by simp only [List.mem_singleton, forall_eq]
            exact hXlt c hb _ _ _ (by rw [Fin.lt_def] at hbc; omega)) h1 h2
    · intro h2; exact ⟨h1, h2⟩
  | H b c hbc =>
    have hb := hlev0 c (fun h => by rw [lev_H_of_le hbc h]; exact lev0_le_H le_rfl)
    have hc0 : 0 < (c : ℕ) := by rw [Fin.lt_def] at hbc; omega
    revert h2
    simp only [bw]
    split_ifs with h0
    · intro h2
      have hc1 : 1 < (c : ℕ) := by rw [Fin.lt_def] at hbc; omega
      simp only [bwH0, dif_pos hc1] at h2 ⊢
      exact palin_path [Gen.X ⟨0, by omega⟩ b h0,
          Gen.X ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def]),
          Gen.X ⟨0, by omega⟩ c (by simp [Fin.lt_def]; omega),
          Gen.X ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])]
        (Gen.H ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def]))
        (by
          intro g hg
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl | rfl
          · exact hXlt c hb _ _ _ (by rw [Fin.lt_def] at hbc; omega)
          · exact hXlt c hb _ _ _ (by simp; omega)
          · exact hXlt c hb _ _ _ le_rfl
          · exact hXlt c hb _ _ _ (by simp; omega)) h1 h2
    · intro h2
      unfold bwH0 at h2 ⊢
      by_cases hc1 : 1 < (c : ℕ)
      · rw [dif_pos hc1] at h2 ⊢
        exact palin_path [Gen.X ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def]),
            Gen.X ⟨0, by omega⟩ c (by simp [Fin.lt_def]; omega),
            Gen.X ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])]
          (Gen.H ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def]))
          (by
            intro g hg
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl | rfl
            · exact hXlt c hb _ _ _ (by simp; omega)
            · exact hXlt c hb _ _ _ le_rfl
            · exact hXlt c hb _ _ _ (by simp; omega)) h1 h2
      · rw [dif_neg hc1] at h2 ⊢
        exact ⟨h1, h2⟩

/-! ### Lemma A.7 (Main Lemma) -/

/-- The conclusion of the Main Lemma at the state `s` and the generator
`g`: with `N` the first syllable of `s` and `t = ⟦N⟧ s`, normal syllables
`N'` from `⟦g⟧ s` to a state `q`, a path `G'` from `t` to `q` strictly
below `s`, and `N' g ≈ G' N`. -/
def MainSquare (s : O n) (g : Gen n) : Prop :=
  ∃ (q : O n) (N' G' : List (Gen n)),
    nw (sem n g * s) = nw q * FreeMonoid.ofList N' ∧
    run G' (FreeMonoid.lift (sem n) (syl s) * s) = q ∧
    PathLt (lev s) G' (FreeMonoid.lift (sem n) (syl s) * s) ∧
    Derivable Fig6 (FreeMonoid.ofList N' * FreeMonoid.of g) (FreeMonoid.ofList G' * syl s)

/-- Lemma A.7 (Main Lemma). -/
theorem main_lemma (s : O n) (hs : s ≠ 1) (g : Gen n) (hg : Basic g) : MainSquare s g := by
  sorry

/-! ### Lemma A.8 and completeness -/

theorem col_one (j : Fin n) : col (1 : O n) j = Pi.single j 1 := by
  funext i; simp [col, one_apply, Pi.single_apply]

theorem piv_of_lev {M : O n} {a : ℕ} {b : ℕ ×ₗ ℕ} (h : lev M = toLex (a, b)) : piv M = a :=
  congrArg (fun l => (ofLex l).1) h

/-- The syllable of a basic generator is the generator itself. -/
theorem syl_basic (g : Gen n) (hg : Basic g) : syl (sem n g) = FreeMonoid.of g := by
  classical
  cases g with
  | Z a =>
    simp only [Basic] at hg
    obtain ⟨a, ha⟩ := a
    simp only at hg; subst hg
    have hp : piv (sem n (Gen.Z ⟨0, ha⟩)) = 1 := by
      have := lev_Z_of_le (t := 1) (p := ⟨0, ha⟩) (by rw [piv_eq_zero_iff.2 rfl]; try exact Nat.zero_le _)
      rw [mul_one] at this; exact piv_of_lev this
    have hp0 : 0 < piv (sem n (Gen.Z ⟨0, ha⟩)) := by omega
    have hpj : pj _ hp0 = ⟨0, ha⟩ := Fin.ext (by simp only [pj]; omega)
    have hcol : col (sem n (Gen.Z ⟨0, ha⟩)) ⟨0, ha⟩ = Pi.single ⟨0, ha⟩ ((-1 : ℤ) : ℝ) := by
      rw [← mul_one (sem n _), col_sem_mul, col_one]
      funext i; simp only [gv, zv]
      split_ifs with h
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [syl, dif_pos hp0, hpj, hcol,
      sylOf_zero (lde_eq_zero_of_int fun i => ?_) (Or.inr (by simp)) rfl,
      dif_neg (lt_irrefl _), if_pos (by norm_num), one_mul]
    by_cases h : i = ⟨0, ha⟩
    · subst h; exact ⟨-1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | X a b hab =>
    simp only [Basic] at hg
    have hp : piv (sem n (Gen.X a b hab)) = b + 1 := by
      have := lev_X_of_le (t := 1) hab (by rw [piv_eq_zero_iff.2 rfl]; exact Nat.zero_le _)
      rw [mul_one] at this; exact piv_of_lev this
    have hp0 : 0 < piv (sem n (Gen.X a b hab)) := by omega
    have hpj : pj _ hp0 = b := Fin.ext (by simp only [pj]; omega)
    have hcol : col (sem n (Gen.X a b hab)) b = Pi.single a ((1 : ℤ) : ℝ) := by
      rw [← mul_one (sem n _), col_sem_mul, col_one]
      funext i; simp only [gv, xv]
      split_ifs with h1 h2
      · subst h1; simp [Pi.single_apply, ne_of_lt hab, Ne.symm (ne_of_lt hab)]
      · subst h2; simp [Pi.single_apply, ne_of_lt hab, Ne.symm (ne_of_lt hab)]
      · simp [Pi.single_apply, h1, h2]
    rw [syl, dif_pos hp0, hpj, hcol,
      sylOf_zero (lde_eq_zero_of_int fun i => ?_) (Or.inl (by simp)) rfl,
      dif_pos hab, if_neg (by norm_num), mul_one]
    by_cases h : i = a
    · subst h; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | H a b hab =>
    simp only [Basic] at hg
    have hp : piv (sem n (Gen.H a b hab)) = b + 1 := by
      have := lev_H_of_le (t := 1) hab (by rw [piv_eq_zero_iff.2 rfl]; exact Nat.zero_le _)
      rw [mul_one] at this; exact piv_of_lev this
    have hp0 : 0 < piv (sem n (Gen.H a b hab)) := by omega
    have hpj : pj _ hp0 = b := Fin.ext (by simp only [pj]; omega)
    have hcol : col (sem n (Gen.H a b hab)) b = hv a b (Pi.single b 1) := by
      rw [← mul_one (sem n _), col_sem_mul, col_one]; rfl
    obtain ⟨hR, hl, hnum, hodd⟩ := hv_single_facts (ne_of_lt hab)
    set v := hv a b (Pi.single b (1 : ℝ))
    have hk : lde v ≠ 0 := by rw [hl]; norm_num
    have h1 : (oddSet v).Nonempty := ⟨a, by rw [hodd]; simp⟩
    have hm1 : (oddSet v).min' h1 = a := by
      apply le_antisymm ((oddSet v).min'_le a (by rw [hodd]; simp))
      apply (oddSet v).le_min'
      intro y hy; rw [hodd] at hy; simp at hy; rcases hy with rfl | rfl
      · exact le_rfl
      · exact le_of_lt hab
    have hpart : partners v ((oddSet v).min' h1) = {b} := by
      rw [hm1]; ext i
      rw [mem_partners, hnum, mem_singleton]
      simp only [SameOdd]
      constructor
      · rintro ⟨hi, -, hodd', -⟩
        by_contra hib
        simp [ne_of_gt hi, hib] at hodd'
      · rintro rfl
        simp [ne_of_gt hab, hab]
    have h2 : (partners v ((oddSet v).min' h1)).Nonempty := by rw [hpart]; simp
    have hm2 : (partners v ((oddSet v).min' h1)).min' h2 = b := by
      have := (partners v ((oddSet v).min' h1)).min'_mem h2
      exact mem_singleton.1 ((Finset.ext_iff.1 hpart _).1 this)
    have hz : a = ⟨0, by omega⟩ := Fin.ext hg.1
    rw [syl, dif_pos hp0, hpj, hcol]
    rw [sylOf_pos hk h1 h2 a hz (by rw [hm2]; exact hab)]
    generalize hgen : (partners v ((oddSet v).min' h1)).min' h2 = m at *
    subst hm2
    rw [dif_neg (by rw [hm1]; exact lt_irrefl _), mul_one]

/-- The normal word of a basic generator is the generator itself. -/
theorem nw_basic (g : Gen n) (hg : Basic g) : nw (sem n g) = FreeMonoid.of g := by
  have hne : sem n g ≠ 1 := by
    intro h
    have := syl_basic g hg
    rw [h, syl, dif_neg (by rw [piv_eq_zero_iff.2 rfl]; omega)] at this
    exact absurd (congrArg FreeMonoid.toList this) (by simp)
  rw [nw_of_ne hne, syl_basic g hg, FreeMonoid.lift_eval_of, sem_sq, nw_one, one_mul]

/-- Lemma A.8: the square closes at every state and basic generator. -/
theorem basic_step (s : O n) : ∀ g, Basic g → StepAt s g := by
  induction s using (InvImage.wf lev wellFounded_lt).induction with
  | _ s ih =>
    intro g hg
    -- every square strictly below `s` closes (Lemma A.6 and the induction hypothesis)
    have IH : ∀ t g', lev t < lev s → lev (sem n g' * t) < lev s → StepAt t g' := by
      intro t g' ht ht'
      have hp := path_step Basic (fun t'' g'' hb h1 _ => ih t'' h1 g'' hb) (bw g') t
        (bw_basic g') (bw_path t g' ht ht')
      rw [run_bw] at hp
      exact ((Derivable.refl _).mul (bw_deriv g')).trans hp
    by_cases hs : s = 1
    · subst hs
      rw [StepAt, mul_one, nw_basic g hg, nw_one]
      apply Derivable.of
      cases g with
      | Z a => exact Fig6.a1 a
      | X a b h => exact Fig6.a2 h
      | H a b h => exact Fig6.a3 h
    · obtain ⟨q, N', G', hN', hq, hpath, hder⟩ := main_lemma s hs g hg
      have hG := path_step (fun _ => True) (fun t g' _ h1 h2 => IH t g' h1 h2) G' _
        (fun _ _ => trivial) hpath
      rw [hq] at hG
      rw [StepAt, hN', mul_assoc]
      refine ((Derivable.refl (nw q)).mul hder).trans ?_
      rw [← mul_assoc]
      refine (hG.mul (Derivable.refl _)).trans ?_
      rw [nw_of_ne hs]

/-- Every square closes. -/
theorem step_all (s : O n) (g : Gen n) : StepAt s g := by
  have hp := path_step' Basic (fun t g' hb => basic_step t g' hb) (bw g) s (bw_basic g)
  rw [run_bw] at hp
  exact ((Derivable.refl _).mul (bw_deriv g)).trans hp

/-- The normal words of Algorithm 1, with the closing squares. -/
noncomputable def normalWords : NormalWords (Fig6 (n := n)) (sem n) where
  nw := nw
  reduces := nw_reduces
  step := step_all

end QCert.HadamardPi
