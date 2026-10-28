/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Joins

A square of the Main Lemma is closed by a path below `s` between the states
`run A s` and `run B s` reached by two words `A`, `B` with
`syl s ≈ A` and `syl (G s) G ≈ B` (`Join.square`).  `Join s A B` says that
such a path `D` exists: `D A ≈ B`, every state of `D` from `run A s` below
`s`.

Joins are moved around in two ways.
* `Join.extend`: a join of `a A` and `b B` (one more letter on each side,
  both states below `s`, `b` an involution) gives a join of `A` and `B`.
* `Join.transfer`: for a word `m` of signed permutations on indices below
  the pivot, a join at `run m s` of `A'`, `B'` with `A' m ≈ μ A`,
  `B' m ≈ ν B` (`μ`, `ν` signed permutations too) gives a join at `s` of `A`
  and `B`.  The level of `run m s` is at most that of `s`
  (`lev_mono_le`).
-/
import QCert.HadamardPi.Pairs

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-- A path below `s` joining the states `run A s` and `run B s`. -/
def Join (s : O n) (A B : List (Gen n)) : Prop :=
  ∃ D : List (Gen n), Derivable Fig6 (ofList (D ++ A)) (ofList B) ∧ PathLt (lev s) D (run A s)

theorem PathLt.mono {L L' : ℕ ×ₗ (ℕ ×ₗ ℕ)} (hL : L ≤ L') :
    ∀ {w : List (Gen n)} {t : O n}, PathLt L w t → PathLt L' w t
  | [], _, h => lt_of_lt_of_le h hL
  | _ :: _, _, h => ⟨PathLt.mono hL h.1, lt_of_lt_of_le h.2 hL⟩

/-- A join closes the square. -/
theorem Join.square {s : O n} (hs : s ≠ 1) {g : Gen n} (hr : sem n g * s ≠ 1)
    {A B : List (Gen n)} (hA : Derivable Fig6 (syl s) (ofList A))
    (hB : Derivable Fig6 (syl (sem n g * s) * FreeMonoid.of g) (ofList B)) (hJ : Join s A B) :
    MainSquare s g := by
  obtain ⟨D, hD, hP⟩ := hJ
  have ht : FreeMonoid.lift (sem n) (syl s) * s = run A s := by
    rw [run_eq_lift, derivable_sound fig6_sound hA]
  refine square_of hs hr D (by rw [ht]; exact hP) ?_
  refine hB.trans (hD.symm.trans ?_)
  rw [ofList_append]
  exact (Derivable.refl _).mul hA.symm

/-- One more letter on each side. -/
theorem Join.extend {s : O n} {a b : Gen n} {A B : List (Gen n)} (hJ : Join s (a :: A) (b :: B))
    (hb : Derivable Fig6 (ofList [b, b]) 1) (h0 : lev (run A s) < lev s)
    (h1 : lev (run (a :: A) s) < lev s) (h2 : lev (run B s) < lev s) : Join s A B := by
  obtain ⟨D, hD, hP⟩ := hJ
  refine ⟨b :: (D ++ [a]), ?_, ?_⟩
  · have e : b :: (D ++ [a]) ++ A = [b] ++ (D ++ a :: A) := by simp
    rw [e, ofList_append]
    refine ((Derivable.refl _).mul hD).trans ?_
    rw [← ofList_append, show [b] ++ b :: B = [b, b] ++ B from rfl, ofList_append]
    simpa using hb.mul (Derivable.refl (ofList B))
  · have hrun : run (D ++ a :: A) s = run (b :: B) s := run_eq_of_der hD s
    have ha : run [a] (run A s) = run (a :: A) s := by rw [run_cons, run_nil, run_cons]
    refine ⟨(PathLt.append D [a] (run A s)).2 ⟨⟨h0, by rw [ha]; exact h1⟩, by rw [ha]; exact hP⟩, ?_⟩
    rw [run_cons, run_append, ha, ← run_append, hrun, run_cons, sem_sq_assoc]
    exact h2

theorem mono_le {L : ℕ ×ₗ (ℕ ×ₗ ℕ)} :
    ∀ (w : List (Gen n)) (t : O n), (∀ g ∈ w, IsMono g ∧ ∀ i ∈ g.idx, lev0 i ≤ L) →
      lev t ≤ L → lev (run w t) ≤ L
  | [], _, _, h => by simpa using h
  | g :: w, t, hw, h => by
    have ih := mono_le w t (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')) h
    obtain ⟨hm, hi⟩ := hw g List.mem_cons_self
    rw [run_cons]
    cases g with
    | Z p => exact le_trans lev_Z_le_max (max_le ih (hi p (by simp [Gen.idx])))
    | X p q hpq => exact le_trans (lev_X_le_max hpq) (max_le ih (hi q (by simp [Gen.idx])))
    | H p q _ => exact absurd hm id

/-- Transfer along a word of signed permutations. -/
theorem Join.transfer {s : O n} {m μ ν A B A' B' : List (Gen n)}
    (hm : ∀ g ∈ m, IsMono g ∧ ∀ i ∈ g.idx, lev0 i ≤ lev s)
    (hμ : ∀ g ∈ μ, IsMono g ∧ ∀ i ∈ g.idx, lev0 i < lev s)
    (hν : ∀ g ∈ ν, IsMono g ∧ ∀ i ∈ g.idx, lev0 i < lev s)
    (hA : Derivable Fig6 (ofList (A' ++ m)) (ofList (μ ++ A)))
    (hB : Derivable Fig6 (ofList (B' ++ m)) (ofList (ν ++ B)))
    (h0 : lev (run A s) < lev s) (hJ : Join (run m s) A' B') : Join s A B := by
  obtain ⟨D, hD, hP⟩ := hJ
  have hle : lev (run m s) ≤ lev s := mono_le m s hm le_rfl
  have hP' := hP.mono hle
  refine ⟨ν.reverse ++ D ++ μ, ?_, ?_⟩
  · -- `νʳ D μ A ≈ νʳ D A' m ≈ νʳ B' m ≈ νʳ ν B ≈ B`
    have e1 : ν.reverse ++ D ++ μ ++ A = ν.reverse ++ D ++ (μ ++ A) := by simp
    rw [e1, ofList_append]
    refine ((Derivable.refl _).mul hA.symm).trans ?_
    rw [← ofList_append, show ν.reverse ++ D ++ (A' ++ m) = ν.reverse ++ (D ++ A') ++ m by simp,
      ofList_append, ofList_append]
    refine (((Derivable.refl _).mul hD).mul (Derivable.refl _)).trans ?_
    rw [← ofList_append, ← ofList_append, List.append_assoc]
    rw [ofList_append]
    refine ((Derivable.refl _).mul hB).trans ?_
    rw [← ofList_append, ← List.append_assoc, ofList_append]
    simpa using (rev_cancel ν).mul (Derivable.refl (ofList B))
  · have e2 : run μ (run A s) = run A' (run m s) := by
      rw [← run_append, ← run_append]; exact (run_eq_of_der hA s).symm
    have e3 : run D (run A' (run m s)) = run ν (run B s) := by
      rw [← run_append, run_eq_of_der hD, ← run_append, run_eq_of_der hB, run_append]
    have pμ : PathLt (lev s) μ (run A s) := mono_path μ _ hμ h0
    have hend : lev (run ν (run B s)) < lev s := by rw [← e3]; exact hP'.last
    rw [PathLt.append, PathLt.append]
    refine ⟨pμ, by rw [e2]; exact hP', ?_⟩
    rw [e2, e3]
    exact mono_path ν.reverse _ (fun g hg => hν g (List.mem_reverse.1 hg)) hend

end QCert.HadamardPi
