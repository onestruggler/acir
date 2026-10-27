/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Paths of generators, closing squares and the statement of the Main Lemma

* `StepAt M g`: the square at the state `M` and the generator `g` closes,
  `nw (⟦g⟧ M) · g ≈ nw M`.
* `run w t` is the state reached from `t` by the word `w` (the rightmost
  letter acting first), and `PathLt L w t` says that every state on the
  way is strictly below the level `L`.
* `MainSquare s g` is the conclusion of the Main Lemma (Lemma A.7).
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

theorem col_one (j : Fin n) : col (1 : O n) j = Pi.single j 1 := by
  funext i; simp [col, one_apply, Pi.single_apply]

theorem piv_of_lev {M : O n} {a : ℕ} {b : ℕ ×ₗ ℕ} (h : lev M = toLex (a, b)) : piv M = a :=
  congrArg (fun l => (ofLex l).1) h

end QCert.HadamardPi
