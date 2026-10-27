/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): Algorithm 1 and levels

Algorithm 1 (exact synthesis), deterministic: for a state `s ≠ I` with
pivot column `v = s e_j` (`j` the largest index of a non-fixed column,
Definition 3.6) and `k = lde(v)`,

* if `k = 0`, `v = (−1)^τ e_a`; the syllable is `(−1)_[j]` if `a = j` and
  `X_[a,j] (−1)_[a]^τ` if `a < j`;
* if `k > 0`, with `a < b < c < d` the first four odd entries of `2^k v`
  and `(−1)^{τ_i} (2^k v)_i ≡ 1 (mod 4)`, the syllable is
  `K_[a,b,c,d] (−1)_[a]^{τ_a} (−1)_[b]^{τ_b} (−1)_[c]^{τ_c} (−1)_[d]^{τ_d}`.

The level of `s` is `(j, k, ℓ)` (Definition 3.6) with `j` counted from `1`
(`0` for the identity) and `ℓ` the number of odd entries of `2^k v` (`0`
when `k = 0`), ordered lexicographically.  Each syllable lowers the level
(`level_syll_lt`), and the normal word `nw s` is the sequence of
syllables down to the identity: `nw s = nw (N s) · N`.
-/
import QCert.LiRossSelinger.Generation

namespace QCert.LiRossSelinger

open Matrix Classical

variable {n : ℕ}

noncomputable section

/-- Levels, ordered lexicographically. -/
abbrev Level := ℕ ×ₗ (ℕ ×ₗ ℕ)

/-- A level from its three components. -/
abbrev mkLevel (j k l : ℕ) : Level := toLex (j, toLex (k, l))

theorem mkLevel_lt_iff {j k l j' k' l' : ℕ} :
    mkLevel j k l < mkLevel j' k' l' ↔ j < j' ∨ j = j' ∧ (k < k' ∨ k = k' ∧ l < l') := by
  simp [mkLevel, Prod.Lex.toLex_lt_toLex]

/-! ## The pivot -/

theorem fixCols_n (U : O_ZHalf n) : FixCols (mat U) n := fun i hi => absurd i.2 (by omega)

/-- `j` of Definition 3.6, counted from `1`: the least `J` such that every
column `≥ J` is fixed (`0` for the identity). -/
def pivotJ (U : O_ZHalf n) : ℕ := Nat.find ⟨n, fixCols_n U⟩

theorem fixCols_pivotJ (U : O_ZHalf n) : FixCols (mat U) (pivotJ U) := Nat.find_spec _

theorem pivotJ_le (U : O_ZHalf n) : pivotJ U ≤ n := Nat.find_min' _ (fixCols_n U)

theorem pivotJ_le_of (U : O_ZHalf n) {J : ℕ} (h : FixCols (mat U) J) : pivotJ U ≤ J :=
  Nat.find_min' _ h

theorem not_fixCols_pred (U : O_ZHalf n) (h : 0 < pivotJ U) : ¬ FixCols (mat U) (pivotJ U - 1) :=
  Nat.find_min ⟨n, fixCols_n U⟩ (show pivotJ U - 1 < pivotJ U by omega)

theorem pivotJ_eq_zero_iff (U : O_ZHalf n) : pivotJ U = 0 ↔ U = 1 := by
  constructor
  · intro h
    have := fixCols_pivotJ U; rw [h] at this; exact eq_one_of_fixCols_zero U this
  · rintro rfl
    apply Nat.eq_zero_of_le_zero
    apply pivotJ_le_of
    intro i _ r
    show (1 : Matrix (Fin n) (Fin n) ℝ) r i = _
    rw [one_apply]

/-- The pivot index (0-based), when there is a pivot. -/
def pidx (U : O_ZHalf n) (h : 0 < pivotJ U) : Fin n := ⟨pivotJ U - 1, by have := pivotJ_le U; omega⟩

/-- The pivot column (column `pivotJ U - 1`; the zero vector for the identity). -/
def pcol (U : O_ZHalf n) : Fin n → ℝ :=
  fun r => if h : 0 < pivotJ U then mat U r (pidx U h) else 0

theorem pcol_mem (U : O_ZHalf n) (r : Fin n) : pcol U r ∈ ZHalf := by
  unfold pcol; split_ifs
  · exact (mem_unitaryOver).1 U.2 r _
  · exact ZHalf.zero_mem

/-- The least denominator exponent of the pivot column. -/
def lde (U : O_ZHalf n) : ℕ := Nat.find (intAt_exists (pcol U) (pcol_mem U))

theorem intAt_lde (U : O_ZHalf n) : IntAt (pcol U) (lde U) := Nat.find_spec _

theorem lde_le (U : O_ZHalf n) {k : ℕ} (h : IntAt (pcol U) k) : lde U ≤ k := Nat.find_min' _ h

/-- The number of odd entries of `2^k v` (`0` when `k = 0`). -/
def nodd (U : O_ZHalf n) : ℕ := if lde U = 0 then 0 else (oddSet (pcol U) (lde U)).card

/-- The level of a state (Definition 3.6). -/
def level (U : O_ZHalf n) : Level :=
  if pivotJ U = 0 then mkLevel 0 0 0 else mkLevel (pivotJ U) (lde U) (nodd U)

theorem level_eq_zero_iff (U : O_ZHalf n) : level U = mkLevel 0 0 0 ↔ U = 1 := by
  rw [← pivotJ_eq_zero_iff]
  unfold level
  split_ifs with h
  · simp [h]
  · simp [mkLevel, h]

/-! ## The pivot column -/

theorem pcol_eq (U : O_ZHalf n) (h : 0 < pivotJ U) (r : Fin n) : pcol U r = mat U r (pidx U h) := by
  simp [pcol, h]

theorem pidx_val (U : O_ZHalf n) (h : 0 < pivotJ U) : (pidx U h : ℕ) = pivotJ U - 1 := rfl

theorem fixCols_succ_pidx (U : O_ZHalf n) (h : 0 < pivotJ U) :
    FixCols (mat U) ((pidx U h : ℕ) + 1) := by
  rw [pidx_val, Nat.sub_add_cancel h]; exact fixCols_pivotJ U

theorem pcol_norm (U : O_ZHalf n) (h : 0 < pivotJ U) : ∑ r, pcol U r * pcol U r = 1 := by
  simp only [pcol_eq U h]; exact col_norm U _

theorem pcol_zero_above (U : O_ZHalf n) (h : 0 < pivotJ U) (r : Fin n) (hr : (pidx U h : ℕ) < r) :
    pcol U r = 0 := by
  rw [pcol_eq U h]
  exact col_zero_above U (pidx U h).2 (fixCols_succ_pidx U h) r hr

/-- The pivot column is not `e_j`. -/
theorem pcol_ne_unit (U : O_ZHalf n) (h : 0 < pivotJ U) :
    ¬ ∀ r, pcol U r = if r = pidx U h then 1 else 0 := by
  intro hc
  apply not_fixCols_pred U h
  have := fixCols_of_col (mat U) (pidx U h).2 (fixCols_succ_pidx U h)
    (fun r => by rw [← pcol_eq U h]; exact hc r)
  exact this

/-! ## The syllables of Algorithm 1 -/

/-- `τ` with `(−1)^τ z ≡ 1 (mod 4)` for odd `z`. -/
def tau (z : ℤ) : Bool := decide (z % 4 = 3)

/-- The integral pivot column `2^k v`. -/
def wint (U : O_ZHalf n) (r : Fin n) : ℤ := ⌊(2 : ℝ) ^ lde U * pcol U r⌋

theorem wint_spec (U : O_ZHalf n) (r : Fin n) : (2 : ℝ) ^ lde U * pcol U r = wint U r := by
  obtain ⟨z, hz⟩ := intAt_lde U r
  rw [wint, hz, Int.floor_intCast]

/-- The odd entries of `2^k v`. -/
abbrev oddS (U : O_ZHalf n) : Finset (Fin n) := oddSet (pcol U) (lde U)

/-- The first four odd entries (in increasing order). -/
def firstOdd (U : O_ZHalf n) (h4 : 4 ≤ (oddS U).card) (i : Fin 4) : Fin n :=
  (oddS U).orderEmbOfFin rfl ⟨i, by omega⟩

theorem firstOdd_lt (U : O_ZHalf n) (h4 : 4 ≤ (oddS U).card) {i i' : Fin 4} (h : i < i') :
    firstOdd U h4 i < firstOdd U h4 i' :=
  ((oddS U).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 (Fin.lt_def.1 h))

theorem firstOdd_mem (U : O_ZHalf n) (h4 : 4 ≤ (oddS U).card) (i : Fin 4) :
    firstOdd U h4 i ∈ oddS U := Finset.orderEmbOfFin_mem _ rfl _

/-- The signs `(−1)_[x]^{τ_x}` of a syllable on the entries `l`. -/
def signs (U : O_ZHalf n) (l : List (Fin n)) : List (Gen n) :=
  (l.filter fun x => tau (wint U x)).map Gen.neg

/-- The syllable of Algorithm 1 at a state (empty at the identity). -/
def syll (U : O_ZHalf n) : List (Gen n) :=
  if h : 0 < pivotJ U then
    if lde U = 0 then
      if ha : ∃ a, pcol U a ≠ 0 then
        if haJ : ha.choose < pidx U h then
          Gen.x ha.choose (pidx U h) haJ ::
            (if pcol U ha.choose < 0 then [Gen.neg ha.choose] else [])
        else [Gen.neg (pidx U h)]
      else []
    else
      if h4 : 4 ≤ (oddS U).card then
        Gen.k (firstOdd U h4 0) (firstOdd U h4 1) (firstOdd U h4 2) (firstOdd U h4 3)
          (firstOdd_lt U h4 (by decide)) (firstOdd_lt U h4 (by decide))
          (firstOdd_lt U h4 (by decide)) ::
          signs U [firstOdd U h4 0, firstOdd U h4 1, firstOdd U h4 2, firstOdd U h4 3]
      else []
  else []

/-- The state after the syllable. -/
def next (U : O_ZHalf n) : O_ZHalf n := FreeMonoid.lift (sem n) (FreeMonoid.ofList (syll U)) * U

/-! ## Each syllable lowers the level -/

theorem level_lt_of {U V : O_ZHalf n} (hU : 0 < pivotJ U)
    (h : pivotJ V < pivotJ U ∨ pivotJ V = pivotJ U ∧
      (lde V < lde U ∨ lde V = lde U ∧ nodd V < nodd U)) : level V < level U := by
  have hU' : level U = mkLevel (pivotJ U) (lde U) (nodd U) := by
    unfold level; rw [if_neg (by omega)]
  rw [hU']
  unfold level
  split_ifs with hV
  · rw [mkLevel_lt_iff]; left; omega
  · rw [mkLevel_lt_iff]; exact h

theorem odd_of_mem_oddS {U : O_ZHalf n} {x : Fin n} (hx : x ∈ oddS U) : Odd (wint U x) := by
  obtain ⟨_, y, hy, hyo⟩ := Finset.mem_filter.1 hx
  have : wint U x = y := by
    have := (wint_spec U x).symm.trans hy
    exact_mod_cast this
  rwa [this]

theorem mat_next (U : O_ZHalf n) : mat (next U) = ((syll U).map genMat).prod * mat U :=
  mat_word _ _

theorem card_oddS (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : 0 < lde U) : 4 ≤ (oddS U).card := by
  have h4 : 4 ∣ (oddS U).card := four_dvd_card_oddSet (pcol_norm U h) hk (intAt_lde U)
  have hS0 : (oddS U).card ≠ 0 := by
    intro h0
    have hk1 : IntAt (pcol U) (lde U - 1 + 1) := by rw [Nat.sub_add_cancel hk]; exact intAt_lde U
    have hev : ∀ r, r ∉ oddSet (pcol U) (lde U - 1 + 1) := by
      rw [Nat.sub_add_cancel hk]; intro r hr
      rw [Finset.card_eq_zero] at h0
      have : r ∈ oddS U := hr
      rw [h0] at this; simp at this
    have := lde_le U (not_odd_of_intAt_pred hk1 hev)
    omega
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hS0) h4

/-- The `k > 0` syllable on the first four odd entries. -/
theorem syll_pos (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : 0 < lde U) :
    syll U = Gen.k (firstOdd U (card_oddS U h hk) 0) (firstOdd U (card_oddS U h hk) 1)
      (firstOdd U (card_oddS U h hk) 2) (firstOdd U (card_oddS U h hk) 3)
      (firstOdd_lt U _ (by decide)) (firstOdd_lt U _ (by decide)) (firstOdd_lt U _ (by decide)) ::
      signs U [firstOdd U (card_oddS U h hk) 0, firstOdd U (card_oddS U h hk) 1,
        firstOdd U (card_oddS U h hk) 2, firstOdd U (card_oddS U h hk) 3] := by
  rw [syll, dif_pos h, if_neg (Nat.pos_iff_ne_zero.1 hk), dif_pos (card_oddS U h hk)]

/-- The `k > 0` syllable keeps the later columns, keeps `2^k v` integral and
makes the four odd entries even. -/
theorem next_pos (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : 0 < lde U) :
    FixCols (mat (next U)) (pivotJ U) ∧
      IntAt (fun r => mat (next U) r (pidx U h)) (lde U) ∧
      (oddSet (fun r => mat (next U) r (pidx U h)) (lde U)).card + 4 ≤ (oddS U).card := by
  set h4 := card_oddS U h hk
  set a := firstOdd U h4 0
  set b := firstOdd U h4 1
  set c := firstOdd U h4 2
  set d := firstOdd U h4 3
  have hab : a < b := firstOdd_lt U h4 (by decide)
  have hbc : b < c := firstOdd_lt U h4 (by decide)
  have hcd : c < d := firstOdd_lt U h4 (by decide)
  set J := pidx U h
  have hz : ∀ r, 2 ^ lde U * mat U r J = wint U r := fun r => by
    rw [← pcol_eq U h]; exact wint_spec U r
  have hsub : ∀ x ∈ [a, b, c, d], x ∈ oddS U := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact firstOdd_mem U h4 _
  obtain ⟨p1, p2, p3⟩ := syllable hab hbc hcd (mat U) J (wint U) hz
    (odd_of_mem_oddS (hsub a (by simp))) (odd_of_mem_oddS (hsub b (by simp)))
    (odd_of_mem_oddS (hsub c (by simp))) (odd_of_mem_oddS (hsub d (by simp)))
  have hmat : mat (next U) = genMat (Gen.k a b c d hab hbc hcd) *
      ((([a, b, c, d].filter fun x => decide (wint U x % 4 = 3)).map
        fun x => genMat (Gen.neg x)).prod * mat U) := by
    rw [mat_next, syll_pos U h hk, List.map_cons, List.prod_cons, Matrix.mul_assoc, signs,
      List.map_map]
    rfl
  have hle : ∀ x ∈ oddS U, x.val ≤ J.val := fun x hx => by
    by_contra hlt
    exact ne_zero_of_mem_oddSet hx (pcol_zero_above U h x (by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro i hi r
    have hfixU := fixCols_pivotJ U
    rw [hmat, p3 i (fun x hx => by
      rw [hfixU i hi x, if_neg (fun e => by
        have := hle x (hsub x hx); rw [e] at this; simp [J, pidx_val] at this; omega)]) r]
    exact hfixU i hi r
  · intro r
    by_cases hr : r ∈ [a, b, c, d]
    · obtain ⟨y, hy, _⟩ := p2 r hr
      exact ⟨y, by show 2 ^ lde U * mat (next U) r J = _; rw [hmat]; exact hy⟩
    · exact ⟨wint U r, by show 2 ^ lde U * mat (next U) r J = _; rw [hmat, p1 r hr]; exact hz r⟩
  · have hodd' : oddSet (fun r => mat (next U) r J) (lde U) ⊆ oddS U \ {a, b, c, d} := by
      intro r hr
      rw [Finset.mem_sdiff]
      by_cases hr4 : r ∈ [a, b, c, d]
      · exfalso
        obtain ⟨y, hy, hye⟩ := p2 r hr4
        obtain ⟨_, y', hy', hyo⟩ := Finset.mem_filter.1 hr
        have : y' = y := by
          rw [hmat] at hy'
          exact_mod_cast hy'.symm.trans hy
        rw [this] at hyo; exact (Int.not_odd_iff_even.2 hye) hyo
      · refine ⟨?_, by simpa using hr4⟩
        obtain ⟨_, y', hy', hyo⟩ := Finset.mem_filter.1 hr
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, y', ?_, hyo⟩
        rw [pcol_eq U h, ← hy']
        simp only
        rw [hmat, p1 r hr4]
    have hT : ({a, b, c, d} : Finset (Fin n)) ⊆ oddS U := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      exact hsub x (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
    have hTcard : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
        simp only [ne_eq, Fin.ext_iff]; simp only [Fin.lt_def] at hab hbc hcd; omega
      obtain ⟨h1, h2, h3, h4', h5, h6⟩ := hne
      rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
        Finset.card_insert_of_notMem (by simp [h4', h5]),
        Finset.card_insert_of_notMem (by simp [h6]), Finset.card_singleton]
    have := Finset.card_le_card hodd'
    rw [Finset.card_sdiff_of_subset hT, hTcard] at this
    omega

/-- The pivot of a state with the pivot column of `U` (all later columns
fixed): its pivot column is the same column. -/
theorem pivot_same {U V : O_ZHalf n} (h : 0 < pivotJ U) (hfix : FixCols (mat V) (pivotJ U))
    (hV : pivotJ V = pivotJ U) (r : Fin n) :
    pcol V r = mat V r (pidx U h) := by
  rw [pcol_eq V (by omega)]
  congr 1
  exact Fin.ext (by simp [pidx_val, hV])

theorem level_next_pos (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : 0 < lde U) :
    level (next U) < level U := by
  obtain ⟨hfix, hint, hcard⟩ := next_pos U h hk
  apply level_lt_of h
  rcases Nat.lt_or_eq_of_le (pivotJ_le_of _ hfix) with hlt | heq
  · left; exact hlt
  · right
    refine ⟨heq, ?_⟩
    have hcol : pcol (next U) = fun r => mat (next U) r (pidx U h) :=
      funext (pivot_same h hfix heq)
    have hle : lde (next U) ≤ lde U := lde_le _ (by rw [hcol]; exact hint)
    rcases Nat.lt_or_eq_of_le hle with hl | hl
    · left; exact hl
    · right
      refine ⟨hl, ?_⟩
      unfold nodd
      rw [if_neg (by omega), if_neg (by omega), hl, hcol]
      change _ < (oddS U).card
      omega

theorem genMat_x_mul_swap {a b : Fin n} (hab : a < b) (M : Matrix (Fin n) (Fin n) ℝ)
    (r c : Fin n) : (genMat (Gen.x a b hab) * M) r c = M (Equiv.swap a b r) c := by
  rw [genMat_x_mul, Equiv.swap_apply_def]
  split_ifs <;> rfl

/-- A generator does not touch the index `i`. -/
def Avoids (g : Gen n) (i : Fin n) : Prop :=
  match g with
  | .neg a => a ≠ i
  | .x a b _ => a ≠ i ∧ b ≠ i
  | .k a b c d _ _ _ => a ≠ i ∧ b ≠ i ∧ c ≠ i ∧ d ≠ i

/-- Generators not touching `i` keep a column `e_i`. -/
theorem col_unit_of_avoid (l : List (Gen n)) (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hM : ∀ r, M r i = if r = i then 1 else 0) (hl : ∀ g ∈ l, Avoids g i) (r : Fin n) :
    ((l.map genMat).prod * M) r i = if r = i then 1 else 0 := by
  induction l generalizing r with
  | nil => simpa using hM r
  | cons g l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.mul_assoc]
    have ih' := ih (fun g' hg' => hl g' (by simp [hg']))
    have hg := hl g (by simp)
    cases g with
    | neg a =>
      exact levelMat_mul_unit (f := ![a]) _ _ (fun p => by fin_cases p; exact hg) ih' r
    | x a b h =>
      exact levelMat_mul_unit (f := ![a, b]) _ _
        (fun p => by fin_cases p; exacts [hg.1, hg.2]) ih' r
    | k a b c d h₁ h₂ h₃ =>
      exact levelMat_mul_unit (f := ![a, b, c, d]) _ _
        (fun p => by fin_cases p; exacts [hg.1, hg.2.1, hg.2.2.1, hg.2.2.2]) ih' r

/-- With `lde = 0` the pivot column is `±e_a`. -/
theorem pcol_unit (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : lde U = 0) :
    ∃ a, (pcol U a = 1 ∨ pcol U a = -1) ∧ ∀ r, r ≠ a → pcol U r = 0 :=
  int_unit (pcol_norm U h) (hk ▸ intAt_lde U)

/-- The `k = 0` syllable fixes the pivot column. -/
theorem next_zero (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : lde U = 0) :
    FixCols (mat (next U)) (pivotJ U - 1) := by
  obtain ⟨a₀, hva₀, hrest₀⟩ := pcol_unit U h hk
  have ha : ∃ a, pcol U a ≠ 0 := ⟨a₀, by rcases hva₀ with e | e <;> rw [e] <;> norm_num⟩
  set a := ha.choose with hadef
  have haa : a = a₀ := by
    by_contra hne; exact ha.choose_spec (hrest₀ a hne)
  rw [← haa] at hva₀ hrest₀
  set J := pidx U h
  have hfix := fixCols_pivotJ U
  have hfix1 : FixCols (mat U) (J.val + 1) := fixCols_succ_pidx U h
  have hJv : (J : ℕ) = pivotJ U - 1 := rfl
  have haJ : a.val ≤ J.val := by
    by_contra hlt; exact (ha.choose_spec) (pcol_zero_above U h a (by omega))
  have hv : ∀ r, mat U r J = pcol U r := fun r => (pcol_eq U h r).symm
  rw [show pivotJ U - 1 = J.val from rfl]
  refine fixCols_of_col _ J.2 ?_ ?_
  · -- the later columns
    intro i hi r
    rw [mat_next]
    have hiJ : J ≠ i := fun e => by rw [← e] at hi; omega
    have hai : a ≠ i := fun e => by rw [← e] at hi; omega
    refine col_unit_of_avoid _ _ i (fun r' => hfix1 i hi r') ?_ r
    unfold syll
    rw [dif_pos h, if_pos hk, dif_pos ha]
    have hai' : ha.choose ≠ i := hai
    have hiJ' : pidx U h ≠ i := hiJ
    split_ifs <;> simp [Avoids, hiJ', hai']
  · -- the pivot column becomes `e_J`
    intro r
    rw [mat_next]
    unfold syll
    rw [dif_pos h, if_pos hk, dif_pos ha]
    have hva : pcol U a = 1 ∨ pcol U a = -1 := hva₀
    by_cases hlt : a < J
    · have hne : a ≠ J := ne_of_lt hlt
      rw [dif_pos hlt, List.map_cons, List.prod_cons, Matrix.mul_assoc, genMat_x_mul_swap]
      have hs : ∀ r', ((((if pcol U a < 0 then [Gen.neg a] else []) : List (Gen n)).map
          genMat).prod * mat U) r' J = if r' = a then 1 else 0 := by
        intro r'
        by_cases hneg : pcol U a < 0
        · rw [if_pos hneg]
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [genMat_neg_mul, hv]
          by_cases hr' : r' = a
          · rw [if_pos hr', if_pos hr', hr']
            rcases hva with e | e <;> rw [e] at hneg ⊢ <;>
              first | (norm_num; done) | exact absurd hneg (by norm_num)
          · rw [if_neg hr', if_neg hr', hrest₀ r' hr']
        · rw [if_neg hneg, List.map_nil, List.prod_nil, Matrix.one_mul, hv]
          by_cases hr' : r' = a
          · rw [if_pos hr', hr']
            rcases hva with e | e <;> rw [e] at hneg ⊢ <;>
              first | (norm_num; done) | exact absurd hneg (by norm_num)
          · rw [if_neg hr', hrest₀ r' hr']
      rw [hs]
      by_cases hrJ : r = J
      · rw [hrJ, Equiv.swap_apply_right, if_pos rfl, if_pos rfl]
      · rw [if_neg hrJ, if_neg]
        intro e
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at e
        exact hrJ e
    · have haJ' : a = J := Fin.ext (le_antisymm haJ (Fin.le_def.1 (Fin.not_lt.1 hlt)))
      rw [dif_neg hlt]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [genMat_neg_mul]
      have hvJ : pcol U J = -1 := by
        rcases hva with e | e
        · exfalso
          apply pcol_ne_unit U h
          intro r'
          by_cases hr' : r' = J
          · rw [if_pos hr', hr', ← haJ', e]
          · rw [if_neg hr', hrest₀ r' (by rw [haJ']; exact hr')]
        · rw [← haJ']; exact e
      by_cases hrJ : r = J
      · rw [if_pos hrJ, if_pos hrJ, hrJ, hv, hvJ]; norm_num
      · rw [if_neg hrJ, if_neg hrJ, hv, hrest₀ r (by rw [haJ']; exact hrJ)]

theorem level_next_zero (U : O_ZHalf n) (h : 0 < pivotJ U) (hk : lde U = 0) :
    level (next U) < level U :=
  level_lt_of h (Or.inl (lt_of_le_of_lt (pivotJ_le_of _ (next_zero U h hk)) (by omega)))

/-- Each syllable of Algorithm 1 lowers the level. -/
theorem level_next_lt (U : O_ZHalf n) (hU : U ≠ 1) : level (next U) < level U := by
  have h : 0 < pivotJ U := Nat.pos_of_ne_zero (fun e => hU ((pivotJ_eq_zero_iff U).1 e))
  rcases Nat.eq_zero_or_pos (lde U) with hk | hk
  · exact level_next_zero U h hk
  · exact level_next_pos U h hk

end

end QCert.LiRossSelinger
