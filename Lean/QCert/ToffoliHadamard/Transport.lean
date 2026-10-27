/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): transport along permutations of the indices

Li–Ross–Selinger's relations come in families whose instances differ by a
renaming of the indices (Section 5.1 of the paper: valid reindexings).
Over the macro alphabet a renaming is a conjugation by `S₈`:

* `adj`: for an adjacent transposition `s_j` that does not exchange two
  indices of a generator `g`, `T_j · enc g · T_j = enc (s_j g)`
  (`MacroTable.adjTable`, 630 equations);
* `transport`: hence, along a path of such transpositions, conjugating
  `enc g` by the word of the path gives the encoding of the renamed
  generator, and `transport_rel` carries a relation to its renamed
  instance, provided every step is valid for every generator of the
  relation;
* `pal`: the encoding of `X_[a,b]` is the word of the palindromic path
  `a, …, b-1, …, a`, so `X_[a,b] g = (τ_{a,b} g) X_[a,b]` whenever that path
  is valid for `g`.

Generators are given by their indices (`AG`, `Gens.lean`).
-/
import QCert.ToffoliHadamard.MacroTable

namespace QCert.ToffoliHadamard.Macro

open Engine

/-- One adjacent transposition. -/
theorem adj {g : AG} {j : ℕ} (hg : g ∈ allAG) (hj : j < 7) (hv : g.valid j = true) :
    g.act j ∈ allAG ∧ Derivable MRel (FreeMonoid.ofList ([.T j] ++ g.enc ++ [.T j]))
      (FreeMonoid.ofList (g.act j).enc) := by
  have h1 := List.all_eq_true.1 adj_keys g hg
  have h2 := allBelow_spec h1 hj
  simp only [hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.contains_iff_mem,
    List.any_eq_true, beq_iff_eq] at h2
  obtain ⟨hmem, c, hc, rfl, rfl⟩ := h2
  exact ⟨hmem, by simpa [AdjCert.entry] using adj_valid c hc⟩

/-! ## Paths -/

/-- The word of a path `j₁, …, jₘ` (`s_{j₁}` applied first): `T_{jₘ} ⋯ T_{j₁}`. -/
def pathW : List ℕ → List ML
  | [] => []
  | j :: P => pathW P ++ [.T j]

theorem sq_mem : ∀ j : Fin 7, ([.T j, .T j], ([] : List ML)) ∈ coxM ++ fig7M := by decide

theorem sq {j : ℕ} (hj : j < 7) :
    Derivable MRel (FreeMonoid.ofList [.T j, .T j]) 1 :=
  Derivable.of (MRel.ax (sq_mem ⟨j, hj⟩))

/-- `l · rev l ≈ ε` for a word in the `T j`, `j < 7`. -/
theorem tw_cancel (l : List ML) (hl : ∀ x ∈ l, ∃ j < 7, x = .T j) :
    Derivable MRel (FreeMonoid.ofList (l ++ l.reverse)) 1 := by
  induction l with
  | nil => simp; rfl
  | cons x l ih =>
    obtain ⟨j, hj, rfl⟩ := hl x (by simp)
    have h1 := derivable_middle (Γ := MRel) (ih (fun y hy => hl y (by simp [hy]))) [.T j] [.T j]
    have e1 : [ML.T j] ++ (l ++ l.reverse) ++ [.T j] = .T j :: l ++ (.T j :: l).reverse := by simp
    rw [e1] at h1
    refine h1.trans ?_
    simpa using sq hj

theorem pathW_T (P : List ℕ) (hP : ∀ j ∈ P, j < 7) : ∀ x ∈ pathW P, ∃ j < 7, x = .T j := by
  induction P with
  | nil => simp [pathW]
  | cons j P ih =>
    intro x hx
    simp only [pathW, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih (fun i hi => hP i (by simp [hi])) x hx
    · exact ⟨j, hP j (by simp), rfl⟩

theorem pathW_cancel (P : List ℕ) (hP : ∀ j ∈ P, j < 7) :
    Derivable MRel (FreeMonoid.ofList (pathW P ++ (pathW P).reverse)) 1 :=
  tw_cancel _ (pathW_T P hP)

theorem pathW_cancel' (P : List ℕ) (hP : ∀ j ∈ P, j < 7) :
    Derivable MRel (FreeMonoid.ofList ((pathW P).reverse ++ pathW P)) 1 := by
  have := tw_cancel (pathW P).reverse (by
    intro x hx; exact pathW_T P hP x (List.mem_reverse.1 hx))
  simpa using this

/-- Conjugating the encoding of `g` by the word of a valid path gives the
encoding of the renamed generator. -/
theorem transport : ∀ (P : List ℕ) (g : AG), g ∈ allAG → (∀ j ∈ P, j < 7) →
    g.validPath P = true →
    Derivable MRel (FreeMonoid.ofList (pathW P ++ g.enc ++ (pathW P).reverse))
      (FreeMonoid.ofList (g.actPath P).enc) := by
  intro P
  induction P with
  | nil => intro g _ _ _; simp [pathW, AG.actPath]; rfl
  | cons j P ih =>
    intro g hg hP hv
    simp only [AG.validPath, Bool.and_eq_true] at hv
    have hj : j < 7 := hP j (by simp)
    have h1 := derivable_middle (adj hg hj hv.1).2 (pathW P) (pathW P).reverse
    have e1 : pathW P ++ ([.T j] ++ g.enc ++ [.T j]) ++ (pathW P).reverse =
        pathW (j :: P) ++ g.enc ++ (pathW (j :: P)).reverse := by simp [pathW]
    rw [e1] at h1
    exact h1.trans (ih (g.act j) (adj hg hj hv.1).1
      (fun i hi => hP i (by simp [hi])) hv.2)

/-- The encoding of a list of generators. -/
def encL (l : List AG) : List ML := l.flatMap AG.enc

theorem conj_list (P : List ℕ) (hP : ∀ j ∈ P, j < 7) : ∀ l : List AG,
    (∀ g ∈ l, g ∈ allAG ∧ g.validPath P = true) →
    Derivable MRel (FreeMonoid.ofList (encL (l.map (AG.actPath P))))
      (FreeMonoid.ofList (pathW P ++ encL l ++ (pathW P).reverse)) := by
  intro l
  induction l with
  | nil =>
    intro _
    simpa [encL] using (pathW_cancel P hP).symm
  | cons g l ih =>
    intro hl
    have hg := hl g (by simp)
    have h1 := (transport P g hg.1 hP hg.2).symm
    have h2 := ih (fun g' hg' => hl g' (by simp [hg']))
    have h3 := h1.mul h2
    simp only [← FreeMonoid.ofList_append] at h3
    refine (by simpa [encL] using h3 : Derivable MRel _ _).trans ?_
    -- P g P' P l P' ≈ P g l P'
    have h4 := derivable_middle (pathW_cancel' P hP) (pathW P ++ g.enc) (encL l ++ (pathW P).reverse)
    simpa [encL] using h4

/-- A relation carried along a path valid for all its generators. -/
theorem transport_rel (P : List ℕ) (hP : ∀ j ∈ P, j < 7) (l r : List AG)
    (hv : ∀ g ∈ l ++ r, g ∈ allAG ∧ g.validPath P = true)
    (h : Derivable MRel (FreeMonoid.ofList (encL l)) (FreeMonoid.ofList (encL r))) :
    Derivable MRel (FreeMonoid.ofList (encL (l.map (AG.actPath P))))
      (FreeMonoid.ofList (encL (r.map (AG.actPath P)))) := by
  have hl := conj_list P hP l (fun g hg => hv g (by simp [hg]))
  have hr := conj_list P hP r (fun g hg => hv g (by simp [hg]))
  have hm := derivable_middle h (pathW P) (pathW P).reverse
  exact hl.trans (hm.trans hr.symm)

/-! ## Checking a family -/

/-- `P` carries the relation `L = R` to `Lt = Rt`. -/
def ok (P : List ℕ) (L R Lt Rt : List AG) : Bool :=
  P.all (· < 7) && (L ++ R).all (fun g => allAG.contains g && g.validPath P) &&
    L.map (AG.actPath P) == Lt && R.map (AG.actPath P) == Rt

theorem of_ok {P : List ℕ} {L R Lt Rt : List AG} (hok : ok P L R Lt Rt = true)
    (h : Derivable MRel (FreeMonoid.ofList (encL L)) (FreeMonoid.ofList (encL R))) :
    Derivable MRel (FreeMonoid.ofList (encL Lt)) (FreeMonoid.ofList (encL Rt)) := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at hok
  obtain ⟨⟨⟨hP, hv⟩, rfl⟩, rfl⟩ := hok
  exact transport_rel P hP L R (fun g hg => hv g hg) h

/-! ## Paths by bubble sort -/

/-- Where each cell goes: the cell of the `i`-th index of the standard
instance goes to the `i`-th index of the target, the free cells to the
free targets in order. -/
def arrange (s t : List ℕ) : List ℕ :=
  let free := (List.range 8).filter (· ∉ s)
  let freeT := (List.range 8).filter (· ∉ t)
  (List.range 8).map fun p =>
    match s.idxOf? p with
    | some i => t.getD i 0
    | none => freeT.getD (free.idxOf p) 0

/-- One pass of bubble sort, carrying the largest element `a` seen so far,
from position `i`: the new list and the swaps. -/
def bpass (a : ℕ) : List ℕ → ℕ → List ℕ × List ℕ
  | [], _ => ([a], [])
  | b :: rest, i =>
    if b < a then
      let r := bpass a rest (i + 1)
      (b :: r.1, i :: r.2)
    else
      let r := bpass b rest (i + 1)
      (a :: r.1, r.2)

/-- One pass over a list. -/
def bpass0 : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | a :: l => bpass a l 0

/-- The swaps of `n` passes of bubble sort. -/
def bubble : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | n + 1, l => (bpass0 l).2 ++ bubble n (bpass0 l).1

/-- A path taking the indices `s` to `t`. -/
def path (s t : List ℕ) : List ℕ := bubble 8 (arrange s t)

/-! ## Palindromes -/

/-- The path `a, a+1, …, b-1, b-2, …, a`, the transposition `(a b)`. -/
def palPath (a b : ℕ) : List ℕ := List.range' a (b - a) ++ (List.range' a (b - a - 1)).reverse

set_option maxRecDepth 10000 in
theorem pal_all : (allBelow 8 fun a => allBelow 8 fun b => !decide (a < b) ||
    (pathW (palPath a b) == xabM a b && (xabM a b).reverse == xabM a b &&
      (palPath a b).all (· < 7))) = true := by decide +kernel

theorem pal_word {a b : ℕ} (hab : a < b) (hb : b < 8) :
    pathW (palPath a b) = xabM a b ∧ (xabM a b).reverse = xabM a b ∧ ∀ j ∈ palPath a b, j < 7 := by
  have h := imp_spec (allBelow_spec (allBelow_spec pal_all (by omega : a < 8)) hb) hab
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- `X_[a,b] g = (τ_{a,b} g) X_[a,b]` when the palindromic path is valid for `g`. -/
theorem pal {a b : ℕ} (hab : a < b) (hb : b < 8) {g : AG} (hg : g ∈ allAG)
    (hv : g.validPath (palPath a b) = true) :
    Derivable MRel (FreeMonoid.ofList (xabM a b ++ g.enc))
      (FreeMonoid.ofList ((g.actPath (palPath a b)).enc ++ xabM a b)) := by
  have hw := pal_word hab hb
  have hP := hw.2.2
  have ht := transport _ g hg hP hv
  simp only [hw.1, hw.2.1] at ht
  -- X g ≈ X g X X ≈ g' X
  have hc : Derivable MRel (FreeMonoid.ofList (xabM a b ++ xabM a b)) 1 := by
    have := pathW_cancel (palPath a b) hP
    rwa [hw.1, hw.2.1] at this
  have h1 := derivable_middle hc (xabM a b ++ g.enc) []
  have h2 := derivable_middle ht [] (xabM a b)
  simp only [List.nil_append, List.append_nil] at h1 h2
  rw [← List.append_assoc] at h1
  exact h1.symm.trans (by simpa using h2)

end QCert.ToffoliHadamard.Macro
