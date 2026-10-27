/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Windows: words acting on a few entries of the pivot column

A word acting on the entries of a *window* `W` (a few indices below the
pivot) changes the pivot column only there.  If, at the least denominator
exponent `k` of the pivot column of `s`, the new column still has numerators
`u'` (so its exponent is at most `k`), equal to the old ones outside `W`, and
fewer odd ones inside `W`, then the new state is strictly below `s`
(`lev_lt_of_window`): the comparison is with the whole column, entries
outside the window included.

The numerators along a word are computed exactly by the *scaled action*
`scw` on `ℤ√2`-vectors: `H_[p,q]` adds and subtracts the two entries and
multiplies the others by `√2` (raising the exponent by one), `X` swaps and
`(-1)` negates (`toReal_scw`).  Along an order embedding of a window of four
indices, the scaled action is computed on `Fin 4` (`scw_map`).
-/
import QCert.HadamardPi.MainLemma
import QCert.HadamardPi.Embed

namespace QCert.HadamardPi

open Matrix Finset FreeMonoid

variable {n : ℕ}

/-! ### The global level comparison -/

theorem card_filter_split {α : Type*} [Fintype α] [DecidableEq α] (W : Finset α) (g : α → Prop)
    [DecidablePred g] :
    (univ.filter g).card = (W.filter g).card + ((univ \ W).filter g).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext i; by_cases h : i ∈ W <;> simp [h]
  · exact disjoint_filter_filter disjoint_sdiff

/-- A new pivot column whose numerators at the old exponent agree outside a
window and have fewer odd ones inside it is strictly lower. -/
theorem lev_lt_of_window {s : O n} (hs : s ≠ 1) (hk : lde (col s (pj s (piv_pos hs))) ≠ 0)
    {t : O n} (hpiv : piv t ≤ piv s) (W : Finset (Fin n)) {u' : Fin n → ℤ√2}
    (hu' : ∀ i, toReal (u' i) = Real.sqrt 2 ^ lde (col s (pj s (piv_pos hs))) *
      col t (pj s (piv_pos hs)) i)
    (hout : ∀ i ∉ W, u' i = num (col s (pj s (piv_pos hs))) i)
    (hcount : (W.filter fun i => Odd (u' i).re).card <
      (W.filter fun i => Odd (num (col s (pj s (piv_pos hs))) i).re).card) :
    lev t < lev s := by
  classical
  have hp := piv_pos hs
  rcases lt_or_eq_of_le hpiv with h | h
  · exact lev_lt_of_piv_lt h
  apply lev_lt_iff.2; right; refine ⟨h, ?_⟩
  have hp' : 0 < piv t := h ▸ hp
  have hpj : pj t hp' = pj s hp := Fin.ext (by simp only [pj]; rw [h])
  rw [pcol_eq hp', hpj, pcol_eq hp]
  set v := col s (pj s hp)
  set w := col t (pj s hp)
  have hR : InRing w := col_inRing t _
  have hle : lde w ≤ lde v := lde_le fun i => ⟨u' i, hu' i⟩
  apply kl_lt_iff.2
  rcases lt_or_eq_of_le hle with hl | hl
  · exact Or.inl hl
  right; refine ⟨hl, ?_⟩
  have hnum : num w = u' := num_eq hR (by rw [hl]; exact hu')
  rw [hl, if_neg hk, if_neg hk]
  have e1 : (oddSet w).card = (W.filter fun i => Odd (u' i).re).card +
      ((univ \ W).filter fun i => Odd (u' i).re).card := by
    rw [← card_filter_split]; congr 1; ext i; rw [mem_oddSet, hnum]; simp
  have e2 : (oddSet v).card = (W.filter fun i => Odd (num v i).re).card +
      ((univ \ W).filter fun i => Odd (num v i).re).card := by
    rw [← card_filter_split]; rfl
  have e3 : ((univ \ W).filter fun i => Odd (u' i).re) =
      ((univ \ W).filter fun i => Odd (num v i).re) := by
    ext i; simp only [mem_filter, mem_sdiff, mem_univ, true_and]
    constructor
    · rintro ⟨hi, ho⟩; exact ⟨hi, by rwa [← hout i hi]⟩
    · rintro ⟨hi, ho⟩; exact ⟨hi, by rwa [hout i hi]⟩
  rw [e1, e2, e3]
  omega

/-! ### The scaled action -/

/-- One letter on numerators: the exponent grows by one for `H`. -/
def scg : Gen n → (Fin n → ℤ√2) → (Fin n → ℤ√2)
  | .Z p, U => fun i => if i = p then -U i else U i
  | .X p q _, U => fun i => if i = p then U q else if i = q then U p else U i
  | .H p q _, U => fun i => if i = p then U p + U q else if i = q then U p - U q else rt2 * U i

/-- The number of `H` letters. -/
def hcnt : Gen n → ℕ
  | .H _ _ _ => 1
  | _ => 0

/-- A word (in written order, the rightmost letter acting first) on
numerators. -/
def scw : List (Gen n) → (Fin n → ℤ√2) → (Fin n → ℤ√2)
  | [], U => U
  | g :: w, U => scg g (scw w U)

/-- The number of `H` letters of a word. -/
def hcntw : List (Gen n) → ℕ
  | [] => 0
  | g :: w => hcnt g + hcntw w

theorem toReal_scg (g : Gen n) {U : Fin n → ℤ√2} {x : Fin n → ℝ} {K : ℕ}
    (h : ∀ i, toReal (U i) = Real.sqrt 2 ^ K * x i) (i : Fin n) :
    toReal (scg g U i) = Real.sqrt 2 ^ (K + hcnt g) * gv g x i := by
  cases g with
  | Z p =>
    simp only [scg, hcnt, gv, zv, add_zero]
    split_ifs with h1
    · subst h1; rw [map_neg, h]; ring
    · exact h i
  | X p q _ =>
    simp only [scg, hcnt, gv, xv, add_zero]
    split_ifs
    · exact h q
    · exact h p
    · exact h i
  | H p q _ =>
    simp only [scg, hcnt, gv, hv]
    split_ifs
    · exact den_hsum (h p) (h q)
    · exact den_hdiff (h p) (h q)
    · rw [map_mul, toReal_rt2, h i, pow_succ]; ring

theorem toReal_scw : ∀ (w : List (Gen n)) {U : Fin n → ℤ√2} {x : Fin n → ℝ} {K : ℕ},
    (∀ i, toReal (U i) = Real.sqrt 2 ^ K * x i) →
      ∀ i, toReal (scw w U i) = Real.sqrt 2 ^ (K + hcntw w) * wv (ofList w) x i
  | [], _, _, _, h, i => by simpa [scw, hcntw] using h i
  | g :: w, U, x, K, h, i => by
    rw [ofList_cons, wv_mul, wv_of, scw, hcntw, toReal_scg g (toReal_scw w h) i,
      show K + (hcnt g + hcntw w) = K + hcntw w + hcnt g by omega]

/-- Away from the letters of a word, the numerators are only rescaled. -/
theorem scw_out : ∀ (w : List (Gen n)) (U : Fin n → ℤ√2) (i : Fin n),
    (∀ g ∈ w, i ∉ g.idx) → scw w U i = rt2 ^ hcntw w * U i
  | [], U, i, _ => by simp [scw, hcntw]
  | g :: w, U, i, h => by
    have hg := h g List.mem_cons_self
    have ih := scw_out w U i fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    cases g with
    | Z p =>
      simp only [Gen.idx, mem_singleton] at hg
      simp [scw, scg, hg, ih, hcntw, hcnt]
    | X p q _ =>
      simp only [Gen.idx, mem_insert, mem_singleton, not_or] at hg
      simp [scw, scg, hg.1, hg.2, ih, hcntw, hcnt]
    | H p q _ =>
      simp only [Gen.idx, mem_insert, mem_singleton, not_or] at hg
      simp only [scw, scg, if_neg hg.1, if_neg hg.2, ih, hcntw, hcnt]
      ring

/-! ### Windows of four indices -/

theorem scg_map {m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (g : Gen m) (V : Fin n → ℤ√2)
    (i : Fin m) : scg (Gen.map f hf g) V (f i) = scg g (V ∘ f) i := by
  have hi := hf.injective
  cases g with
  | Z p => simp [scg, Gen.map, hi.eq_iff]
  | X p q _ => simp [scg, Gen.map, hi.eq_iff]
  | H p q _ => simp [scg, Gen.map, hi.eq_iff]

theorem scw_map {m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) :
    ∀ (w : List (Gen m)) (V : Fin n → ℤ√2) (i : Fin m),
      scw (w.map (Gen.map f hf)) V (f i) = scw w (V ∘ f) i
  | [], V, i => rfl
  | g :: w, V, i => by
    rw [List.map_cons, scw, scg_map]
    simp only [scw]
    congr 1
    funext j
    exact scw_map f hf w V j

theorem hcntw_map {m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) :
    ∀ w : List (Gen m), hcntw (w.map (Gen.map f hf)) = hcntw w
  | [] => rfl
  | g :: w => by
    rw [List.map_cons, hcntw, hcntw, hcntw_map f hf w]
    cases g <;> rfl

theorem idx_map {m : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (g : Gen m) {i : Fin n}
    (hi : i ∈ (Gen.map f hf g).idx) : ∃ j, f j = i := by
  cases g with
  | Z p => simp only [Gen.map, Gen.idx, mem_singleton] at hi; exact ⟨p, hi.symm⟩
  | X p q _ =>
    simp only [Gen.map, Gen.idx, mem_insert, mem_singleton] at hi
    rcases hi with e | e
    · exact ⟨p, e.symm⟩
    · exact ⟨q, e.symm⟩
  | H p q _ =>
    simp only [Gen.map, Gen.idx, mem_insert, mem_singleton] at hi
    rcases hi with e | e
    · exact ⟨p, e.symm⟩
    · exact ⟨q, e.symm⟩

end QCert.HadamardPi
