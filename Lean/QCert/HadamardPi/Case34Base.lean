/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The nodes of Clément's Case 3.4

A node of the case analysis (`Case34.lean`) is a state `s` whose pivot
column has, on the window `0, …, w-1`, numerators given by a pattern
(`WinPat`), and outside it numerators divisible by `√2 ^ δ` (`TailD`); its
goal is the join of `A = H_[1,3] H_[0,2]` and `B = H_[1,3] H_[0,2] H_[0,1]`
on the window (`wJ`).  Here: the commutation of words on disjoint indices,
the restriction of a window (`shrink_window`), and the tail facts.
-/
import QCert.HadamardPi.SymClean
import QCert.HadamardPi.Case34Der

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-- The window of `s` has the pattern `P` at the parameters `t`. -/
abbrev WinPat {w : ℕ} (s : O n) (hs : s ≠ 1) (hw : w ≤ piv s) (P : List ZL) (t : ℕ → ℤ) : Prop :=
  ∀ j : Fin w, num (col s (pj s (piv_pos hs))) (Fin.castLE (hw.trans (piv_le_n s)) j) =
    zev (P.getD j dZ) t

/-- The entries of `s` outside the window are divisible by `√2 ^ δ`. -/
abbrev TailD (s : O n) (hs : s ≠ 1) (w δ : ℕ) : Prop :=
  ∀ i : Fin n, w ≤ (i : ℕ) → ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i

/-- The join of two words on the window. -/
abbrev wJ {w : ℕ} (s : O n) (hw : w ≤ piv s) (A B : List (Gen w)) : Prop :=
  Join s (A.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
      (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))
    (B.map (Gen.map (Fin.castLE (hw.trans (piv_le_n s)))
      (Fin.strictMono_castLE (hw.trans (piv_le_n s)))))

theorem TailD.mono {s : O n} {hs : s ≠ 1} {w δ : ℕ} (h : TailD s hs w (δ + 1)) : TailD s hs w δ :=
  fun i hi => by
    obtain ⟨y, hy⟩ := h i hi
    exact ⟨rt2 * y, by rw [← hy, pow_succ]; ring⟩

theorem TailD.castLE {s : O n} {hs : s ≠ 1} {w δ : ℕ} (h : TailD s hs w δ) (hwn : w ≤ n) :
    ∀ i, (∀ j : Fin w, Fin.castLE hwn j ≠ i) →
      ∃ y, rt2 ^ δ * y = num (col s (pj s (piv_pos hs))) i :=
  fun i hi => h i ((castLE_ne_iff hwn i).1 hi)

theorem not_odd_of_rt2 {δ : ℕ} (hδ : 1 ≤ δ) {u : ℤ√2} (h : ∃ y, rt2 ^ δ * y = u) : ¬Odd u.re := by
  obtain ⟨y, rfl⟩ := h
  obtain ⟨d, rfl⟩ : ∃ d, δ = d + 1 := ⟨δ - 1, by omega⟩
  rw [pow_succ, mul_comm (rt2 ^ d), mul_assoc, rt2_mul]
  rintro ⟨r, hr⟩
  dsimp only at hr
  omega

/-- Words on disjoint indices commute. -/
theorem comm_word : ∀ (K A : List (Gen n)),
    (∀ g ∈ A, ∀ i ∈ g.idx, ∀ g' ∈ K, ∀ i' ∈ g'.idx, i ≠ i') →
      Derivable Fig6 (ofList (A ++ K)) (ofList (K ++ A))
  | [], A, _ => by simpa using Derivable.refl (ofList A)
  | g :: K, A, h => by
    have h1 := comm_letter g A fun g1 hg1 i hi i' hi' => h g1 hg1 i hi g List.mem_cons_self i' hi'
    have h2 := comm_word K A fun g1 hg1 i hi g' hg' i' hi' =>
      h g1 hg1 i hi g' (List.mem_cons_of_mem _ hg') i' hi'
    have e1 := der_mid [] (A ++ [g]) K ([g] ++ A) h1
    have e2 := der_mid [g] (A ++ K) [] (K ++ A) h2
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.singleton_append,
      List.cons_append] at e1 e2 ⊢
    exact e1.trans e2

/-- The indices of a letter, as a list. -/
def Gen.idxL {w : ℕ} : Gen w → List (Fin w)
  | .Z a => [a]
  | .X a b _ => [a, b]
  | .H a b _ => [a, b]

theorem Gen.mem_idxL {w : ℕ} {g : Gen w} {i : Fin w} : i ∈ g.idx → i ∈ g.idxL := by
  cases g <;> simp [Gen.idx, Gen.idxL]

/-- Disjointness of two words on a window, decided. -/
def disjW {w : ℕ} (A K : List (Gen w)) : Bool :=
  A.all fun g => K.all fun g' => g.idxL.all fun i => g'.idxL.all fun i' => i != i'

theorem comm_word_win {w : ℕ} {A K : List (Gen w)} (h : disjW A K = true) :
    Derivable Fig6 (ofList (A ++ K)) (ofList (K ++ A)) := by
  refine comm_word K A fun g hg i hi g' hg' i' hi' => ?_
  simp only [disjW, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h g hg g' hg' i (Gen.mem_idxL hi) i' (Gen.mem_idxL hi')

/-- The indices of a word on the window are below its size. -/
theorem idx_castLE_lt {w : ℕ} (hwn : w ≤ n) (l : List (Gen w)) :
    ∀ g ∈ l.map (Gen.map (Fin.castLE hwn) (Fin.strictMono_castLE hwn)), ∀ i ∈ g.idx, (i : ℕ) < w := by
  intro g hg i hi
  rw [List.mem_map] at hg
  obtain ⟨g0, -, rfl⟩ := hg
  obtain ⟨j, rfl⟩ := idx_map _ _ g0 hi
  simp

theorem WinPat.take {w : ℕ} {s : O n} {hs : s ≠ 1} {hw : w ≤ piv s} {P : List ZL} {t : ℕ → ℤ}
    (h : WinPat s hs hw P t) : WinPat s hs hw (P.take w) t := by
  intro j
  rw [h j]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos j.2]

theorem lde_eq_of_lev {s s' : O n} (hs : s ≠ 1) (hs' : s' ≠ 1) (h : lev s' = lev s) :
    lde (col s' (pj s' (piv_pos hs'))) = lde (col s (pj s (piv_pos hs))) := by
  have e := congrArg (fun l : ℕ ×ₗ (ℕ ×ₗ ℕ) => (ofLex (ofLex l).2).1) h
  simp only [lev, kl, ofLex_toLex] at e
  rwa [pcol_eq (piv_pos hs'), pcol_eq (piv_pos hs)] at e

/-- Entries `w, …, w'-1` of a pattern divisible by `√2`. -/
def tailDiv (P : List ZL) (w w' : ℕ) : Bool :=
  (List.range (w' - w)).all fun j => (zdivp 1 (P.getD (w + j) dZ)).isSome

/-- Restrict the window `0, …, w'-1` to `0, …, w-1`. -/
theorem shrink_window {w w' δ : ℕ} (hww : w ≤ w') {s : O n} {hs : s ≠ 1} (hw' : w' ≤ piv s)
    {P : List ZL} {t : ℕ → ℤ} (hP : WinPat s hs hw' P t) (htail : TailD s hs w' δ)
    (hδ : 1 ≤ δ) (hd : tailDiv P w w' = true) :
    WinPat s hs (hww.trans hw') P t ∧ TailD s hs w 1 := by
  refine ⟨fun j => hP ⟨j, by omega⟩, fun i hi => ?_⟩
  by_cases h : (i : ℕ) < w'
  · have e := hP ⟨i, h⟩
    have hj : (zdivp 1 (P.getD i dZ)).isSome = true := by
      simp only [tailDiv, List.all_eq_true, List.mem_range] at hd
      have := hd (i - w) (by omega)
      rwa [show w + (i - w) = i by omega] at this
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hj
    refine ⟨zev z t, ?_⟩
    have := zdivp_sound 1 hz t
    simp only [Fin.castLE_mk] at e
    rw [this, ← e]
  · obtain ⟨y, hy⟩ := htail i (by omega)
    obtain ⟨d, rfl⟩ : ∃ d, δ = d + 1 := ⟨δ - 1, by omega⟩
    exact ⟨rt2 ^ d * y, by rw [← hy]; ring⟩

end QCert.HadamardPi
