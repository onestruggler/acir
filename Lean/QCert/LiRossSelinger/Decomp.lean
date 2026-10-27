/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): Lemma A.19, basic decompositions

Every generator is derivably `P g₀ P⁻¹` with `g₀` basic and `P` a word of
adjacent transpositions `X_[i,i+1]` on the indices up to the generator's
extent (the renaming relations (3b)–(3g), as in `PushL`).  Applied to a
state `s`, every intermediate state of this word is a permutation (by `P`'s
letters) of `s` or of `G s`; such a permutation keeps every column beyond
`max(j(s), j(G s))` fixed and permutes the entries of the pivot column, so
it never rises above `max(level s, level (G s))`.  The paper cites Greylyn
(2014) for this lemma.
-/
import QCert.LiRossSelinger.Reduction
import QCert.LiRossSelinger.PushL

namespace QCert.LiRossSelinger

open Matrix Classical

variable {n : ℕ}

noncomputable section

/-! ## Words of transpositions as row permutations -/

/-- `x` is an adjacent transposition `X_[i,i+1]` with `i + 1 ≤ m`. -/
def AdjLe (m : ℕ) : Gen n → Prop
  | .x a b _ => b.val = a.val + 1 ∧ b.val ≤ m
  | _ => False

/-- The permutation of rows of a word of transpositions (letters other than
transpositions count as the identity). -/
def rowPerm : List (Gen n) → Equiv.Perm (Fin n)
  | [] => 1
  | .x a b _ :: l => Equiv.swap a b * rowPerm l
  | _ :: l => rowPerm l

theorem rowPerm_apply (l : List (Gen n)) (hl : ∀ g ∈ l, AdjLe n g) (M : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n) : ((l.map genMat).prod * M) r c = M ((rowPerm l).symm r) c := by
  induction l generalizing r with
  | nil => simp [rowPerm]; rfl
  | cons g l ih =>
    have hg := hl g (by simp)
    have ih' := ih (fun g' h' => hl g' (by simp [h']))
    cases g with
    | x a b hab =>
      rw [List.map_cons, List.prod_cons, Matrix.mul_assoc, genMat_x_mul_swap, ih', rowPerm,
        Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
    | neg a => exact hg.elim
    | k a b c d _ _ _ => exact hg.elim

theorem rowPerm_fix (l : List (Gen n)) (m : ℕ) (hl : ∀ g ∈ l, AdjLe m g) (r : Fin n)
    (hr : m < r.val) : rowPerm l r = r := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    have hg := hl g (by simp)
    have ih' := ih (fun g' h' => hl g' (by simp [h']))
    cases g with
    | x a b hab =>
      rw [rowPerm, Equiv.Perm.mul_apply, ih', Equiv.swap_apply_of_ne_of_ne]
      · intro e; rw [e] at hr; simp [AdjLe] at hg; omega
      · intro e; rw [e] at hr; simp [AdjLe] at hg; omega
    | neg a => exact hg.elim
    | k a b c d _ _ _ => exact hg.elim

theorem rowPerm_symm_fix (l : List (Gen n)) (m : ℕ) (hl : ∀ g ∈ l, AdjLe m g) (r : Fin n)
    (hr : m < r.val) : (rowPerm l).symm r = r := by
  rw [Equiv.symm_apply_eq, rowPerm_fix l m hl r hr]

theorem adjLe_mono {m m' : ℕ} (h : m ≤ m') {g : Gen n} (hg : AdjLe m g) : AdjLe m' g := by
  cases g with
  | x a b _ => exact ⟨hg.1, hg.2.trans h⟩
  | neg a => exact hg.elim
  | k a b c d _ _ _ => exact hg.elim

/-! ## Levels of permuted states -/

/-- The state `σ x` for a word `σ` of transpositions. -/
abbrev permState (l : List (Gen n)) (x : O_ZHalf n) : O_ZHalf n :=
  FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * x

theorem mat_permState (l : List (Gen n)) (hl : ∀ g ∈ l, AdjLe n g) (x : O_ZHalf n) (r c : Fin n) :
    mat (permState l x) r c = mat x ((rowPerm l).symm r) c := by
  rw [mat_word, rowPerm_apply l hl]

theorem fixCols_permState (l : List (Gen n)) (m : ℕ) (hl : ∀ g ∈ l, AdjLe m g) (x : O_ZHalf n)
    {J : ℕ} (hJ : FixCols (mat x) J) (hmJ : m < J) : FixCols (mat (permState l x)) J := by
  have hl' : ∀ g ∈ l, AdjLe n g := fun g hg => by
    have := hl g hg
    cases g with
    | x a b _ => exact ⟨this.1, by have := b.2; omega⟩
    | neg a => exact this.elim
    | k a b c d _ _ _ => exact this.elim
  intro c hc r
  rw [mat_permState l hl' x, hJ c hc]
  congr 1
  apply propext
  rw [Equiv.symm_apply_eq, rowPerm_fix l m hl c (by omega)]

/-- A permutation supported below the pivot keeps the level. -/
theorem level_permState_le (l : List (Gen n)) (m : ℕ) (hl : ∀ g ∈ l, AdjLe m g) (x : O_ZHalf n)
    (hm : m < pivotJ x) : level (permState l x) ≤ level x := by
  have hl' : ∀ g ∈ l, AdjLe n g := fun g hg => by
    have := hl g hg
    cases g with
    | x a b _ => exact ⟨this.1, by have := b.2; omega⟩
    | neg a => exact this.elim
    | k a b c d _ _ _ => exact this.elim
  set y := permState l x
  have hpx : 0 < pivotJ x := by omega
  have hfix := fixCols_permState l m hl x (fixCols_pivotJ x) hm
  rcases Nat.lt_or_eq_of_le (pivotJ_le_of y hfix) with hlt | heq
  · exact (level_lt_of hpx (Or.inl hlt)).le
  · -- same pivot: the pivot column is permuted
    have hcol : ∀ r, pcol y r = pcol x ((rowPerm l).symm r) := by
      intro r
      rw [pivot_same hpx hfix heq, mat_permState l hl' x, pcol_eq x hpx]
    have hint : ∀ k, IntAt (pcol y) k ↔ IntAt (pcol x) k := by
      intro k
      constructor
      · intro h r
        obtain ⟨z, hz⟩ := h (rowPerm l r)
        exact ⟨z, by rw [hcol, Equiv.symm_apply_apply] at hz; exact hz⟩
      · intro h r
        obtain ⟨z, hz⟩ := h ((rowPerm l).symm r)
        exact ⟨z, by rw [hcol]; exact hz⟩
    have hlde : lde y = lde x :=
      le_antisymm (lde_le y ((hint _).2 (intAt_lde x))) (lde_le x ((hint _).1 (intAt_lde y)))
    have hodd : (oddSet (pcol y) (lde y)).card = (oddSet (pcol x) (lde x)).card := by
      rw [hlde]
      apply Finset.card_bij (fun r _ => (rowPerm l).symm r)
      · intro r hr
        obtain ⟨_, z, hz, ho⟩ := Finset.mem_filter.1 hr
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, z, by rw [← hcol]; exact hz, ho⟩
      · intro a _ b _ e; exact (rowPerm l).symm.injective e
      · intro r hr
        refine ⟨rowPerm l r, ?_, by simp⟩
        obtain ⟨_, z, hz, ho⟩ := Finset.mem_filter.1 hr
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, z, by
          rw [hcol, Equiv.symm_apply_apply]; exact hz, ho⟩
    unfold level
    rw [if_neg (by omega), if_neg (by omega), heq]
    unfold nodd
    rw [hlde, ← hodd, hlde]

/-- A permutation supported below `J`, applied to a state fixing the columns
from `J' ≤ J` on: below level `(J, 0, 0)` or exactly there. -/
theorem level_permState_unit (l : List (Gen n)) (m : ℕ) (hl : ∀ g ∈ l, AdjLe m g) (x : O_ZHalf n)
    {J : ℕ} (hmJ : m < J) (hxJ : pivotJ x < J) :
    level (permState l x) ≤ mkLevel J 0 0 := by
  have hl' : ∀ g ∈ l, AdjLe n g := fun g hg => by
    have := hl g hg
    cases g with
    | x a b _ => exact ⟨this.1, by have := b.2; omega⟩
    | neg a => exact this.elim
    | k a b c d _ _ _ => exact this.elim
  set y := permState l x
  have hfixx : FixCols (mat x) J := fun c hc r => fixCols_pivotJ x c (by omega) r
  have hfix := fixCols_permState l m hl x hfixx hmJ
  rcases Nat.lt_or_eq_of_le (pivotJ_le_of y hfix) with hlt | heq
  · unfold level; split_ifs
    · exact (mkLevel_lt_iff.2 (Or.inl (by omega))).le
    · exact (mkLevel_lt_iff.2 (Or.inl hlt)).le
  · -- the pivot column of `y` is a permuted unit column of `x`
    have hpy : 0 < pivotJ y := by omega
    have hcolx : ∀ r, mat x r (pidx y hpy) = if r = pidx y hpy then 1 else 0 :=
      fixCols_pivotJ x _ (by rw [pidx_val, heq]; omega)
    have hint : IntAt (pcol y) 0 := by
      intro r
      rw [pcol_eq y hpy, mat_permState l hl' x, hcolx]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    have hlde : lde y = 0 := Nat.eq_zero_of_le_zero (lde_le y hint)
    unfold level
    rw [if_neg (by omega), heq]
    unfold nodd
    rw [if_pos hlde, hlde]

/-! ## Conjugation forms -/

/-- `g ≈ P g₀ P⁻¹`, `P` adjacent transpositions up to `m`, `g₀` basic. -/
def ConjForm (g : Gen n) (m : ℕ) : Prop :=
  ∃ (P : List (Gen n)) (g₀ : Gen n), (∀ x ∈ P, AdjLe m x) ∧ IsBasic g₀ ∧
    Derivable (Table1 n) (FreeMonoid.of g) (FreeMonoid.ofList (P ++ [g₀] ++ P.reverse))

theorem conjForm_basic {g : Gen n} (hg : IsBasic g) (m : ℕ) : ConjForm g m :=
  ⟨[], g, by simp, hg, by simpa using Derivable.refl (FreeMonoid.of g)⟩

theorem conjForm_mono {g : Gen n} {m m' : ℕ} (h : m ≤ m') (hg : ConjForm g m) : ConjForm g m' := by
  obtain ⟨P, g₀, hP, hb, hd⟩ := hg
  exact ⟨P, g₀, fun x hx => adjLe_mono h (hP x hx), hb, hd⟩

/-- Conjugating a conjugation form by a transposition. -/
theorem conjForm_conj {x y : Gen n} {m : ℕ} (hx : AdjLe m x) (hy : ConjForm y m) {z : Gen n}
    (hz : Derivable (Table1 n) (FreeMonoid.of z) (FreeMonoid.ofList [x, y, x])) : ConjForm z m := by
  obtain ⟨P, g₀, hP, hb, hd⟩ := hy
  refine ⟨x :: P, g₀, ?_, hb, ?_⟩
  · intro w hw; simp only [List.mem_cons] at hw; rcases hw with rfl | hw
    · exact hx
    · exact hP w hw
  · refine hz.trans ?_
    have := ((Derivable.refl (FreeMonoid.of x)).mul hd).mul (Derivable.refl (FreeMonoid.of x))
    simpa [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, mul_assoc] using this

theorem adjLe_x (a : ℕ) {b : ℕ} (hb : b < n) (hab : b = a + 1) :
    AdjLe b (Gen.x (n := n) ⟨a, by omega⟩ ⟨b, hb⟩ (by simp [Fin.lt_def]; omega)) :=
  ⟨by simp [hab], le_rfl⟩

theorem conjForm_neg (a : ℕ) (ha : a < n) : ConjForm (Gen.neg ⟨a, ha⟩) a := by
  induction a with
  | zero => exact conjForm_basic (by simp [IsBasic]) 0
  | succ a ih =>
    exact conjForm_conj (adjLe_x a ha rfl) (conjForm_mono (by omega) (ih (by omega)))
      (conj_of_comm' (Table1.r3c (n := n) ⟨a, by omega⟩ ⟨a + 1, ha⟩ (by simp [Fin.lt_def]))
        (Table1.r1a _ _ _))

theorem conjForm_x (g : ℕ) : ∀ (a b : ℕ) (hg : b = a + g + 1) (hb : b < n),
    ConjForm (Gen.x ⟨a, by omega⟩ ⟨b, hb⟩ (by simp [Fin.lt_def]; omega)) b := by
  induction g with
  | zero => intro a b hg hb; exact conjForm_basic (by simp [IsBasic]; omega) b
  | succ g ih =>
    intro a b hg hb
    exact conjForm_conj (adjLe_x (b - 1) hb (by omega))
      (conjForm_mono (by omega) (ih a (b - 1) (by omega) (by omega)))
      (conj_of_comm (Table1.r3b (n := n) ⟨a, by omega⟩ ⟨b - 1, by omega⟩ ⟨b, hb⟩
        (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _))

theorem conjForm_k (S : ℕ) : ∀ (a b c d : ℕ) (hS : a + b + c + d = S) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hd : d < n),
    ConjForm (Gen.k ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩ (by simp [Fin.lt_def]; omega)
      (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)) d := by
  induction S using Nat.strong_induction_on with
  | _ S ih =>
  intro a b c d hS hab hbc hcd hd
  by_cases h4 : c + 1 < d
  · exact conjForm_conj (adjLe_x (d - 1) hd (by omega))
      (conjForm_mono (by omega) (ih _ (by omega) a b c (d - 1) rfl hab hbc (by omega) (by omega)))
      (conj_of_comm (Table1.r3g ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d - 1, by omega⟩ ⟨d, hd⟩
        (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
        (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _))
  by_cases h3 : b + 1 < c
  · exact conjForm_conj (adjLe_mono (by omega) (adjLe_x (c - 1) (n := n) (by omega) (by omega)))
      (ih _ (by omega) a b (c - 1) d rfl hab (by omega) (by omega) hd)
      (conj_of_comm (Table1.r3f ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c - 1, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩
        (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
        (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _))
  by_cases h2 : a + 1 < b
  · exact conjForm_conj (adjLe_mono (by omega) (adjLe_x (b - 1) (n := n) (by omega) (by omega)))
      (ih _ (by omega) a (b - 1) c d rfl (by omega) (by omega) hcd hd)
      (conj_of_comm (Table1.r3e ⟨a, by omega⟩ ⟨b - 1, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩
        (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
        (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _))
  by_cases h1 : 0 < a
  · exact conjForm_conj (adjLe_mono (by omega) (adjLe_x (a - 1) (n := n) (by omega) (by omega)))
      (ih _ (by omega) (a - 1) b c d rfl (by omega) hbc hcd hd)
      (conj_of_comm (Table1.r3d ⟨a - 1, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩
        (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]; omega)
        (by simp [Fin.lt_def]; omega)) (Table1.r1a _ _ _))
  have ha : a = 0 := by omega
  have hb : b = 1 := by omega
  have hc : c = 2 := by omega
  have hd' : d = 3 := by omega
  subst ha hb hc hd'
  exact conjForm_basic (by simp [IsBasic]) 3

/-- The extent of a generator (its largest index, Definition A.18). -/
def extent : Gen n → ℕ
  | .neg a => a
  | .x _ b _ => b
  | .k _ _ _ d _ _ _ => d

theorem conjForm_gen (g : Gen n) : ConjForm g (extent g) := by
  cases g with
  | neg a => exact conjForm_neg a.val a.isLt
  | x a b h =>
    exact conjForm_x ((b : ℕ) - a - 1) a.val b.val (by have := Fin.lt_def.mp h; omega) b.isLt
  | k a b c d h₁ h₂ h₃ => exact conjForm_k _ a.val b.val c.val d.val rfl h₁ h₂ h₃ d.isLt

/-! ## Lemma A.19 -/

theorem extent_lt (g : Gen n) : extent g < n := by
  cases g with
  | neg a => exact a.isLt
  | x a b _ => exact b.isLt
  | k a b c d _ _ _ => exact d.isLt

/-- A generator moves its extent, so the extent lies below the pivot of
`s` or of `G s`. -/
theorem extent_lt_pivot (s : O_ZHalf n) (g : Gen n) :
    extent g < max (pivotJ s) (pivotJ (sem n g * s)) := by
  by_contra hle
  push Not at hle
  set e : Fin n := ⟨extent g, extent_lt g⟩
  have h1 : ∀ r, mat s r e = if r = e then 1 else 0 :=
    fixCols_pivotJ s e (le_trans (le_max_left _ _) hle)
  have h2 := fixCols_pivotJ (sem n g * s) e (le_trans (le_max_right _ _) hle) e
  rw [if_pos rfl, mat_mul] at h2
  change (genMat g * mat s) e e = 1 at h2
  cases g with
  | neg a =>
    have : e = a := rfl
    rw [genMat_neg_mul, if_pos this, h1, if_pos rfl] at h2; norm_num at h2
  | x a b hab =>
    have : e = b := rfl
    rw [genMat_x_mul, if_neg (by rw [this]; exact ne_of_gt hab), if_pos this, h1,
      if_neg (by rw [this]; exact ne_of_lt hab)] at h2
    norm_num at h2
  | k a b c d h₁ h₂ h₃ =>
    have : e = d := rfl
    have had : a ≠ d := ne_of_lt (h₁.trans (h₂.trans h₃))
    have hbd : b ≠ d := ne_of_lt (h₂.trans h₃)
    have hcd : c ≠ d := ne_of_lt h₃
    rw [genMat_k_mul, if_neg (by rw [this]; exact Ne.symm had),
      if_neg (by rw [this]; exact Ne.symm hbd), if_neg (by rw [this]; exact Ne.symm hcd),
      if_pos this, h1, h1, h1, h1, this, if_neg had, if_neg hbd, if_neg hcd, if_pos rfl] at h2
    norm_num at h2

theorem mkLevel_le_level (x : O_ZHalf n) : mkLevel (pivotJ x) 0 0 ≤ level x := by
  unfold level
  split_ifs with h
  · rw [h]
  · rcases Nat.eq_zero_or_pos (lde x) with hk | hk
    · rcases Nat.eq_zero_or_pos (nodd x) with hl | hl
      · rw [hk, hl]
      · exact (mkLevel_lt_iff.2 (Or.inr ⟨rfl, Or.inr ⟨hk.symm, hl⟩⟩)).le
    · exact (mkLevel_lt_iff.2 (Or.inr ⟨rfl, Or.inl hk⟩)).le

theorem lift_reverse (l : List (Gen n)) :
    FreeMonoid.lift (sem n) (FreeMonoid.ofList l.reverse) * FreeMonoid.lift (sem n) (FreeMonoid.ofList l)
      = 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e1 : FreeMonoid.lift (sem n) (FreeMonoid.ofList (x :: l).reverse) =
        FreeMonoid.lift (sem n) (FreeMonoid.ofList l.reverse) * sem n x := by
      simp [List.reverse_cons, FreeMonoid.ofList_append]
    have e2 : FreeMonoid.lift (sem n) (FreeMonoid.ofList (x :: l)) =
        sem n x * FreeMonoid.lift (sem n) (FreeMonoid.ofList l) := by
      simp [FreeMonoid.ofList_cons]
    rw [e1, e2, mul_assoc, ← mul_assoc (sem n x), sem_sq, one_mul, ih]

theorem isBasic_of_adjLe {m : ℕ} {g : Gen n} (h : AdjLe m g) : IsBasic g := by
  cases g with
  | x a b _ => exact h.1
  | neg a => exact h.elim
  | k a b c d _ _ _ => exact h.elim

/-- Lemma A.19, with the level bound at every intermediate state. -/
theorem lemmaA19 : BasicDecomp n := by
  intro s g
  obtain ⟨P, g₀, hP, hb, hd⟩ := conjForm_gen g
  set m := extent g
  set h := P ++ [g₀] ++ P.reverse with hh
  have hsem : FreeMonoid.lift (sem n) (FreeMonoid.ofList h) = sem n g := by
    have := derivable_sound sound hd; simpa using this.symm
  refine ⟨h, ?_, hd, ?_⟩
  · intro x hx
    simp only [hh, List.mem_append, List.mem_singleton, List.mem_reverse] at hx
    rcases hx with (hx | rfl) | hx
    · exact isBasic_of_adjLe (hP x hx)
    · exact hb
    · exact isBasic_of_adjLe (hP x hx)
  · intro i hi
    set B := max (level s) (level (sem n g * s))
    have hmJ := extent_lt_pivot s g
    -- the bound for a permutation of `s` or of `G s`
    have bound : ∀ x, (x = s ∨ x = sem n g * s) → ∀ q : List (Gen n), (∀ y ∈ q, AdjLe m y) →
        level (permState q x) ≤ B := by
      intro x hx q hq
      by_cases hJ : pivotJ x = max (pivotJ s) (pivotJ (sem n g * s))
      · refine (level_permState_le q m hq x (by rw [hJ]; exact hmJ)).trans ?_
        rcases hx with rfl | rfl
        · exact le_max_left _ _
        · exact le_max_right _ _
      · have hlt : pivotJ x < max (pivotJ s) (pivotJ (sem n g * s)) := by
          rcases hx with rfl | rfl
          · exact lt_of_le_of_ne (le_max_left _ _) hJ
          · exact lt_of_le_of_ne (le_max_right _ _) hJ
        refine (level_permState_unit q m hq x hmJ hlt).trans ?_
        rcases le_total (pivotJ s) (pivotJ (sem n g * s)) with hle | hle
        · rw [max_eq_right hle]; exact (mkLevel_le_level _).trans (le_max_right _ _)
        · rw [max_eq_left hle]; exact (mkLevel_le_level _).trans (le_max_left _ _)
    by_cases hiP : i ≤ P.length
    · -- a permutation of `G s`
      have hdrop : h.drop i = P.drop i ++ [g₀] ++ P.reverse := by
        rw [hh, List.append_assoc, List.drop_append_of_le_length hiP, List.append_assoc]
      have htake : h = P.take i ++ h.drop i := by
        rw [hdrop, ← List.append_assoc, ← List.append_assoc, List.take_append_drop]
      have e : FreeMonoid.lift (sem n) (FreeMonoid.ofList (h.drop i)) =
          FreeMonoid.lift (sem n) (FreeMonoid.ofList (P.take i).reverse) * sem n g := by
        rw [← hsem, htake, FreeMonoid.ofList_append, map_mul, ← mul_assoc, lift_reverse, one_mul,
          ← htake]
      rw [e, mul_assoc]
      exact bound _ (Or.inr rfl) _ (fun y hy => hP y (List.mem_of_mem_take (List.mem_reverse.1 hy)))
    · -- a permutation of `s`
      have hdrop : h.drop i = P.reverse.drop (i - P.length - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, i = (P ++ [g₀]).length + k := ⟨i - P.length - 1, by simp; omega⟩
        rw [hh, hk, List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append]
        congr 1; simp; omega
      rw [hdrop]
      exact bound s (Or.inl rfl) _ (fun y hy => hP y (List.mem_reverse.1 (List.mem_of_mem_drop hy)))

end

end QCert.LiRossSelinger
