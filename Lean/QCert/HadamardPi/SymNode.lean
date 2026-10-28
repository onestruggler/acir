/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Steps of the case analysis on patterns

The case analysis of `CaseFour.lean` is a tree whose nodes are states `s`
with a window `0, …, w-1` of the pivot column described by a pattern, and
the goal of a join `Join s A B` for two fixed words `A`, `B` on the indices
`0, …, 3`.  The steps:

* `leaf_join`: a checked path with a derivation (`join_of_check`) along the
  embedding `Fin.castLE` of the window;
* `transfer_mono`: a transfer along a monomial word on the window
  (`Join.transfer`), the new window being computed (`pat_after`);
* `extend_entry`: an entry outside the window, of depth `δ`, moved next to
  the window by a transposition, which extends the window by one entry with
  two new parameters (`dent`);
* `tail_odd_entry`: an entry outside the window forced by an odd number of
  odd entries in the window (Clément's Lemma 2.1, without classes), and
  `tail_class_even`: an even class count in the window gives an even count
  outside.
-/
import QCert.HadamardPi.SymSplit

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### The embedding of the window -/

theorem map_castLE_castLE {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (l : List (Gen a)) :
    (l.map (Gen.map (Fin.castLE h1) (Fin.strictMono_castLE h1))).map
        (Gen.map (Fin.castLE h2) (Fin.strictMono_castLE h2)) =
      l.map (Gen.map (Fin.castLE (h1.trans h2)) (Fin.strictMono_castLE (h1.trans h2))) := by
  rw [List.map_map]
  congr 1
  funext g
  cases g <;> rfl

theorem castLE_lt {s : O n} {w : ℕ} (hw : w ≤ piv s) (j : Fin w) :
    ((Fin.castLE (hw.trans (piv_le_n s)) j : Fin n) : ℕ) < piv s := by
  simp only [Fin.coe_castLE]; omega

/-- A leaf: a derivation and a checked path on the window. -/
theorem leaf_join {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {D A B : List (Gen w)} (hd : Derivable Fig6 (ofList (D ++ A)) (ofList B))
    (hc : pathOK P D A = true) :
    Join s (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
      (B.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) :=
  join_of_check _ (Fin.strictMono_castLE (hw.trans (piv_le_n s))) hs hk (castLE_lt hw) hP hd hc

/-- The state `A s` of a checked word is below `s`. -/
theorem lev_lt_of_check {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {A : List (Gen w)} (hc : pathOK P [] A = true) :
    lev (run (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
      (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) s) < lev s := by
  have := path_of_check _ (Fin.strictMono_castLE (hw.trans (piv_le_n s))) hs hk (castLE_lt hw) hP
    (D := []) hc
  simpa [PathLt] using this

/-! ### Monomial transfers -/

/-- All letters monomial. -/
def allMono {w : ℕ} : List (Gen w) → Bool
  | [] => true
  | .H _ _ _ :: _ => false
  | _ :: l => allMono l

theorem mono_of_allMono {w : ℕ} : ∀ {l : List (Gen w)}, allMono l = true → ∀ g ∈ l, IsMono g
  | [], _, g, hg => by simp at hg
  | .H _ _ _ :: _, h, _, _ => by simp [allMono] at h
  | .Z a :: l, h, g, hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · trivial
    · exact mono_of_allMono (l := l) (by simpa [allMono] using h) g hg
  | .X a b hab :: l, h, g, hg => by
    rcases List.mem_cons.1 hg with rfl | hg
    · trivial
    · exact mono_of_allMono (l := l) (by simpa [allMono] using h) g hg

theorem allMono_map {w : ℕ} (f : Fin w → Fin n) (hf : StrictMono f) {l : List (Gen w)}
    (h : allMono l = true) : ∀ g ∈ l.map (Gen.map f hf), IsMono g := by
  intro g hg
  rw [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := mono_of_allMono h g0 hg0
  cases g0 <;> simp_all [Gen.map, IsMono]

theorem idx_lt_of_window {w : ℕ} {s : O n} (hw : w ≤ piv s) (l : List (Gen w)) :
    ∀ g ∈ l.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))), ∀ i ∈ g.idx, (i : ℕ) < piv s := by
  intro g hg i hi
  rw [List.mem_map] at hg
  obtain ⟨g0, -, rfl⟩ := hg
  obtain ⟨j, rfl⟩ := idx_map _ _ g0 hi
  exact castLE_lt hw j

/-- A transfer along a monomial word `m` on the window, with
`A' m ≈ μ A` and `B' m ≈ ν B`: a join at `m s`, whose window has the
pattern `divAll P m`, gives one at `s`. -/
theorem transfer_mono {w : ℕ} {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    (hw : w ≤ piv s) {P : List ZL} {t : ℕ → ℤ}
    (hP : ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
      zev (P.getD j dZ) t)
    {T : ℤ√2 → Prop}
    (htail : ∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s (pj s (piv_pos hs))) i))
    {m μ ν A A' B B' : List (Gen w)} (hm : allMono m = true) (hμ : allMono μ = true)
    (hν : allMono ν = true)
    (hA : Derivable Fig6 (ofList (A' ++ m)) (ofList (μ ++ A)))
    (hB : Derivable Fig6 (ofList (B' ++ m)) (ofList (ν ++ B)))
    (hc : allSome P m = true) (j0 : Fin w) (ho : oddSure ((divAll P m).getD j0 dZ) = true)
    (hcA : pathOK P [] A = true)
    (hJ : ∀ (s' : O n) (hs' : s' ≠ 1), lde (col s' (pj s' (piv_pos hs'))) ≠ 0 →
      ∀ hw' : w ≤ piv s',
      (∀ j : Fin w, num (col s' (pj s' (piv_pos hs'))) (Fin.castLE (hw'.trans (piv_le_n s')) j) =
        zev ((divAll P m).getD j dZ) t) →
      (∀ i : Fin n, w ≤ (i : ℕ) → T (num (col s' (pj s' (piv_pos hs'))) i)) →
      Join s' (A'.map (Gen.map (Fin.castLE (hw'.trans (piv_le_n s')))
          (Fin.strictMono_castLE (hw'.trans (piv_le_n s')))))
        (B'.map (Gen.map (Fin.castLE (hw'.trans (piv_le_n s')))
          (Fin.strictMono_castLE (hw'.trans (piv_le_n s')))))) :
    Join s (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
      (B.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
        (Fin.strictMono_castLE (hw.trans (piv_le_n s))))) := by
  set f := Fin.castLE (hw.trans (piv_le_n s))
  have hf : StrictMono f := Fin.strictMono_castLE _
  obtain ⟨hs', hpiv, hl, hwin, htl⟩ := pat_after f hf hs hk (castLE_lt hw) hP m hc j0 ho
  have hw' : w ≤ piv (run (m.map (Gen.map f hf)) s) := by rw [hpiv]; exact hw
  have hJ' := hJ _ hs' (by rw [hl]; exact hk) hw' hwin (fun i hi => by
    rw [htl i (fun j hj => by
      have := j.2; rw [← hj] at hi; simp [f] at hi; omega)]
    exact htail i hi)
  have hidx := idx_lt_of_window hw
  have lev0lt : ∀ l : List (Gen w), ∀ g ∈ l.map (Gen.map f hf), ∀ i ∈ g.idx, lev0 i < lev s :=
    fun l g hg i hi => lev0_lt_of_lde (piv_pos hs) (hidx l g hg i hi) hk
  refine Join.transfer (m := m.map (Gen.map f hf)) (μ := μ.map (Gen.map f hf))
    (ν := ν.map (Gen.map f hf)) (A' := A'.map (Gen.map f hf)) (B' := B'.map (Gen.map f hf))
    (fun g hg => ⟨allMono_map f hf hm g hg, fun i hi => le_of_lt (lev0lt m g hg i hi)⟩)
    (fun g hg => ⟨allMono_map f hf hμ g hg, lev0lt μ g hg⟩)
    (fun g hg => ⟨allMono_map f hf hν g hg, lev0lt ν g hg⟩) ?_ ?_
    (lev_lt_of_check hs hk hw hP hcA) hJ'
  · have := der_map f hf hA; simpa only [List.map_append] using this
  · have := der_map f hf hB; simpa only [List.map_append] using this

/-! ### Parity of a sum -/

theorem card_odd_zmod {ι : Type*} [Fintype ι] (x : ι → ℤ) :
    ((univ.filter fun i => Odd (x i)).card : ZMod 2) = ∑ i, (x i : ZMod 2) := by
  classical
  simp only [intCast_zmod2]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem odd_card_of_odd_sum {ι : Type*} [Fintype ι] (x : ι → ℤ) (h : Odd (∑ i, x i)) :
    Odd (univ.filter fun i => Odd (x i)).card := by
  classical
  have key := card_odd_zmod x
  have h1 : ((∑ i, x i : ℤ) : ZMod 2) = 1 := by rw [intCast_zmod2, if_pos h]
  push_cast at h1
  rw [h1] at key
  rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even, key]
  decide

end QCert.HadamardPi
