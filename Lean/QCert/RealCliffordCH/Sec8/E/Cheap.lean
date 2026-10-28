/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rules of Figure 8 that decode by definition

The decoding `decW` (Definition 8.3) maps each side of Equations (20),
(21), (25)–(28), (30), (33), (34), (35) and (42) of Figure 8 to the same
circuit: these rules hold by the definitions alone (`decW u = decW v`).
-/
import QCert.RealCliffordCH.Sec8.Statement

namespace QCert.RealCliffordCH.Sec8.E

open Circuit

variable {n : ℕ}

/-! ## Indices and letters -/

theorem ix_val {v : ℕ} (h : v < 2 ^ n) : (ix n v : ℕ) = v := Nat.mod_eq_of_lt h

theorem ix_ne {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : a ≠ b) : ix n a ≠ ix n b := by
  intro e; apply h; rw [← ix_val ha, ← ix_val hb, e]

theorem decW_wordOf (l : List (PG (2 ^ n))) : decW n (wordOf l) = (l.map (dec n)).prod :=
  FreeMonoid.lift_ofList _ _

theorem dec_Zz {a c : ℕ} (ha : a < 2 ^ n) (hc : c < 2 ^ n) : dec n (Zz n a c) = dZZ n a c := by
  simp [dec, Zz, ix_val ha, ix_val hc]

theorem dec_Zx {a c d : ℕ} (ha : a < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n) (hcd : c ≠ d) :
    dec n (Zx n a c d) = dZX n a c d := by
  simp [dec, Zx, ix_ne hc hd hcd, ix_val ha, ix_val hc, ix_val hd]

theorem dec_Xx {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (hab : a ≠ b) (hcd : c ≠ d) :
    dec n (Xx n a b c d) = drawn [dZX n b c d, dZX n a a b] := by
  simp [dec, Xx, ix_ne ha hb hab, ix_ne hc hd hcd, ix_val ha, ix_val hb, ix_val hc, ix_val hd]

theorem drawn_two (x y : Circ n) : drawn [x, y] = y * x := by simp [drawn]

theorem drawn_three (x y z : Circ n) : drawn [x, y, z] = z * (y * x) := by
  simp [drawn, mul_assoc]

/-! ## `dZXab` unfolded -/

theorem dZXab_one (s a : ℕ) : dZXab n 1 s a (a + 1) = dZX1 n a (if s = a then 0 else 1) := by
  simp [dZXab]

theorem dZXab_odd (f s a b : ℕ) (h1 : b ≠ a + 1) (h2 : (b - a) % 2 = 1) :
    dZXab n (f + 1) s a b =
      if s = a then drawn [dZX1 n a 0, dZXab n f (a + 1) (a + 1) b, dZX1 n a 1]
      else drawn [dZX1 n a 0, dZXab n f b (a + 1) b, dZX1 n a 1] := by
  simp [dZXab, h1, h2]

theorem dZXab_even (f s a b : ℕ) (h1 : b ≠ a + 1) (h2 : (b - a) % 2 = 0) :
    dZXab n (f + 1) s a b =
      if s = a then drawn [dZX1 n (b - 1) 1, dZXab n f a a (b - 1), dZX1 n (b - 1) 0]
      else drawn [dZX1 n (b - 1) 1, dZXab n f (b - 1) a (b - 1), dZX1 n (b - 1) 0] := by
  have : ¬ (b - a) % 2 = 1 := by omega
  simp [dZXab, h1, this]

/-- `D((-1)_[s]X_[a,b])` for `a < b` and `s ∈ {a, b}`. -/
theorem dZX_lt {s a b : ℕ} (hab : a < b) (hs : s = a ∨ s = b) :
    dZX n s a b = dZXab n (b - a) s a b := by
  simp [dZX, hs, min_eq_left hab.le, max_eq_right hab.le]

/-- `D((-1)_[s]X_[b,a])` for `a < b` and `s ∈ {a, b}`. -/
theorem dZX_gt {s a b : ℕ} (hab : a < b) (hs : s = a ∨ s = b) :
    dZX n s b a = dZXab n (b - a) s a b := by
  have : s = b ∨ s = a := hs.symm
  simp [dZX, this, min_eq_right hab.le, max_eq_left hab.le]

/-! ## The rules -/

/-- (20) decodes by definition. -/
theorem dec20 (a : ℕ) (ha : a < 2 ^ n) : decW n (wordOf [Zz n a a]) = decW n (wordOf []) := by
  simp [decW_wordOf, dec_Zz ha ha, dZZ, drawn]

/-- (21) decodes by definition. -/
theorem dec21 (a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    decW n (wordOf [Zz n a b]) = decW n (wordOf [Zz n b a]) := by
  simp only [decW_wordOf, List.map, dec_Zz ha hb, dec_Zz hb ha, dZZ, max_comm, min_comm]

/-- (25) decodes by definition. -/
theorem dec25 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (hodd : (c - a) % 2 = 1) :
    decW n (wordOf [Zx n a a c]) =
      decW n (wordOf [Zx n (a + 1) a (a + 1), Zx n (a + 1) (a + 1) c, Zx n a a (a + 1)]) := by
  have h1 : a + 1 < 2 ^ n := by omega
  have h0 : a < 2 ^ n := by omega
  obtain ⟨f, hf⟩ : ∃ f, c - a = f + 1 := ⟨c - a - 1, by omega⟩
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx h0 h0 hc (by omega), dec_Zx h1 h0 h1 (by omega), dec_Zx h1 h1 hc (by omega),
    dec_Zx h0 h0 h1 (by omega)]
  rw [dZX_lt (by omega) (Or.inl rfl), dZX_lt (by omega) (Or.inr rfl),
    dZX_lt (by omega) (Or.inl rfl), dZX_lt (by omega) (Or.inl rfl), hf,
    dZXab_odd f a a c (by omega) (by omega), if_pos rfl, drawn_three,
    show a + 1 - a = 1 by omega, show c - (a + 1) = f by omega, dZXab_one, dZXab_one]
  simp

/-- (26) decodes by definition. -/
theorem dec26 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (hodd : (c - a) % 2 = 1) :
    decW n (wordOf [Zx n c a c]) =
      decW n (wordOf [Zx n (a + 1) a (a + 1), Zx n c (a + 1) c, Zx n a a (a + 1)]) := by
  have h1 : a + 1 < 2 ^ n := by omega
  have h0 : a < 2 ^ n := by omega
  obtain ⟨f, hf⟩ : ∃ f, c - a = f + 1 := ⟨c - a - 1, by omega⟩
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx hc h0 hc (by omega), dec_Zx h1 h0 h1 (by omega), dec_Zx hc h1 hc (by omega),
    dec_Zx h0 h0 h1 (by omega)]
  rw [dZX_lt (by omega) (Or.inr rfl), dZX_lt (by omega) (Or.inr rfl),
    dZX_lt (by omega) (Or.inr rfl), dZX_lt (by omega) (Or.inl rfl), hf,
    dZXab_odd f c a c (by omega) (by omega), if_neg (by omega), drawn_three,
    show a + 1 - a = 1 by omega, show c - (a + 1) = f by omega, dZXab_one, dZXab_one]
  simp

/-- (27) decodes by definition. -/
theorem dec27 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (heven : (c - a) % 2 = 0) :
    decW n (wordOf [Zx n a a c]) =
      decW n (wordOf [Zx n (c - 1) (c - 1) c, Zx n a a (c - 1), Zx n c (c - 1) c]) := by
  obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : b < 2 ^ n := by omega
  have h0 : a < 2 ^ n := by omega
  obtain ⟨f, hf⟩ : ∃ f, b + 1 - a = f + 1 := ⟨b - a, by omega⟩
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx h0 h0 hc (by omega), dec_Zx h1 h1 hc (by omega), dec_Zx h0 h0 h1 (by omega),
    dec_Zx hc h1 hc (by omega)]
  rw [dZX_lt (by omega) (Or.inl rfl), dZX_lt (by omega) (Or.inl rfl),
    dZX_lt (by omega) (Or.inl rfl), dZX_lt (by omega) (Or.inr rfl), hf,
    dZXab_even f a a (b + 1) (by omega) (by omega), if_pos rfl, drawn_three,
    show b + 1 - b = 1 by omega, show b - a = f by omega, Nat.add_sub_cancel, dZXab_one,
    dZXab_one]
  simp

/-- (28) decodes by definition. -/
theorem dec28 (a c : ℕ) (hac : a + 1 < c) (hc : c < 2 ^ n) (heven : (c - a) % 2 = 0) :
    decW n (wordOf [Zx n c a c]) =
      decW n (wordOf [Zx n (c - 1) (c - 1) c, Zx n (c - 1) a (c - 1), Zx n c (c - 1) c]) := by
  obtain ⟨b, rfl⟩ : ∃ b, c = b + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 : b < 2 ^ n := by omega
  have h0 : a < 2 ^ n := by omega
  obtain ⟨f, hf⟩ : ∃ f, b + 1 - a = f + 1 := ⟨b - a, by omega⟩
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx hc h0 hc (by omega), dec_Zx h1 h1 hc (by omega), dec_Zx h1 h0 h1 (by omega),
    dec_Zx hc h1 hc (by omega)]
  rw [dZX_lt (by omega) (Or.inr rfl), dZX_lt (by omega) (Or.inl rfl),
    dZX_lt (by omega) (Or.inr rfl), dZX_lt (by omega) (Or.inr rfl), hf,
    dZXab_even f (b + 1) a (b + 1) (by omega) (by omega), if_neg (by omega), drawn_three,
    show b + 1 - b = 1 by omega, show b - a = f by omega, Nat.add_sub_cancel, dZXab_one,
    dZXab_one]
  simp

/-- (30) decodes by definition. -/
theorem dec30 (a b c : ℕ) (hb : b < 2 ^ n) (ha : a < 2 ^ n) (hc : c < 2 ^ n) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) :
    decW n (wordOf [Zx n c a b]) = decW n (wordOf [Zz n c a, Zx n a a b]) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx hc ha hb hab, dec_Zx ha ha hb hab, dec_Zz hc ha]
  simp [dZX, hca, hcb, drawn]

/-- (33) decodes by definition. -/
theorem dec33 (a b : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : a ≠ b) :
    decW n (wordOf [Zx n b a b]) = decW n (wordOf [Zx n b b a]) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx hb ha hb hab, dec_Zx hb hb ha (Ne.symm hab)]
  simp [dZX, max_comm, min_comm]

/-- (34) decodes by definition. -/
theorem dec34 (a b c d : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (hab : a ≠ b) (hcd : c ≠ d) :
    decW n (wordOf [Xx n a b c d]) = decW n (wordOf [Zx n a a b, Zx n b c d]) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Xx ha hb hc hd hab hcd, dec_Zx ha ha hb hab, dec_Zx hb hc hd hcd, drawn_two]

/-! ## (42): the fresh pair -/

theorem dec_Hh {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n) (hd : d < 2 ^ n)
    (hab : a ≠ b) (hcd : c ≠ d) :
    dec n (Hh n a b c d) =
      if Distinct4 a b c d then dHH4 n a b c d
      else drawn [dHH4 n (freshPair n a b c d).1 (freshPair n a b c d).2 c d,
        dHH4 n a b (freshPair n a b c d).1 (freshPair n a b c d).2] := by
  simp [dec, Hh, ix_ne ha hb hab, ix_ne hc hd hcd, ix_val ha, ix_val hb, ix_val hc, ix_val hd]

/-- The two smallest indices outside `{a, b, c, d}` are distinct indices outside it. -/
theorem freshPair_spec (a b c d : ℕ) (hn : 3 ≤ n) :
    (freshPair n a b c d).1 < 2 ^ n ∧ (freshPair n a b c d).2 < 2 ^ n ∧
      (freshPair n a b c d).1 ≠ (freshPair n a b c d).2 ∧
      (freshPair n a b c d).1 ≠ a ∧ (freshPair n a b c d).1 ≠ b ∧
      (freshPair n a b c d).1 ≠ c ∧ (freshPair n a b c d).1 ≠ d ∧
      (freshPair n a b c d).2 ≠ a ∧ (freshPair n a b c d).2 ≠ b ∧
      (freshPair n a b c d).2 ≠ c ∧ (freshPair n a b c d).2 ≠ d := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set p : ℕ → Bool := fun e => decide (e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d) with hp
  set l := (List.range (2 ^ n)).filter p with hl
  have hnd : l.Nodup := List.Nodup.filter _ List.nodup_range
  have hq : ((List.range (2 ^ n)).filter (fun e => !p e)).length ≤ 4 := by
    have hnd' : ((List.range (2 ^ n)).filter (fun e => !p e)).Nodup :=
      List.Nodup.filter _ List.nodup_range
    have hsub : (List.range (2 ^ n)).filter (fun e => !p e) ⊆ [a, b, c, d] := by
      intro x hx
      simp only [List.mem_filter, hp, Bool.not_eq_true', decide_eq_false_iff_not] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      by_contra h
      push_neg at h
      exact hx.2 h
    simpa using (List.subperm_of_subset hnd' hsub).length_le
  have hlen : 2 ≤ l.length := by
    have := List.length_eq_length_filter_add (l := List.range (2 ^ n)) p
    simp only [List.length_range] at this
    rw [← hl] at this
    omega
  obtain ⟨e, f, r, hefr⟩ : ∃ e f r, l = e :: f :: r := by
    match l, hlen with
    | e :: f :: r, _ => exact ⟨e, f, r, rfl⟩
  have hfp : freshPair n a b c d = (e, f) := by
    unfold freshPair
    rw [← hl, hefr]
  have he : e ∈ l := by rw [hefr]; simp
  have hf : f ∈ l := by rw [hefr]; simp
  have hef : e ≠ f := by
    have := hnd; rw [hefr] at this
    intro h; subst h; simp at this
  rw [hl, List.mem_filter, List.mem_range] at he hf
  simp only [hp, decide_eq_true_eq] at he hf
  rw [hfp]
  exact ⟨he.1, hf.1, hef, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2, hf.2.1, hf.2.2.1,
    hf.2.2.2.1, hf.2.2.2.2⟩

/-- (42) decodes by definition. -/
theorem dec42 (hn : 3 ≤ n) (a b c d : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) (hab : a ≠ b) (hcd : c ≠ d) (h3 : ¬ Distinct4 a b c d) :
    decW n (wordOf [Hh n a b (freshPair n a b c d).1 (freshPair n a b c d).2,
        Hh n (freshPair n a b c d).1 (freshPair n a b c d).2 c d]) =
      decW n (wordOf [Hh n a b c d]) := by
  obtain ⟨he, hf, hef, hea, heb, hec, hed, hfa, hfb, hfc, hfd⟩ := freshPair_spec a b c d hn
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Hh ha hb he hf hab hef, dec_Hh he hf hc hd hef hcd, dec_Hh ha hb hc hd hab hcd,
    if_neg h3, drawn_two]
  rw [if_pos (by unfold Distinct4; omega), if_pos (by unfold Distinct4; omega)]

/-! ## (35): the words `Σ`, `Σ'` and the gadget -/

theorem tau_lt {N e k i v : ℕ} (hk : k < N) (hi : i < N) (hv : v < N) : tau e k i v < N := by
  unfold tau; split_ifs <;> assumption

theorem mem_L {p : PG (2 ^ n)} {m k i : ℕ}
    (h : p ∈ (if (if k ≠ i then 1 else 0) = 1 then [Zx n m k i] else [])) :
    p = Zx n m k i ∧ k ≠ i := by
  by_cases hki : k ≠ i
  · rw [if_pos hki, if_pos rfl, List.mem_singleton] at h; exact ⟨h, hki⟩
  · rw [if_neg hki, if_neg (by decide)] at h; nomatch h

/-- The letters of `Σ_{a,b,c,d}` and `Σ'_{a,b,c,d}` are proper letters `(-1)_[m]X_[k,i]`. -/
theorem sigma_mem (hn : 3 ≤ n) {a b c d : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) (p : PG (2 ^ n))
    (hp : p ∈ (sigmaW n a b c d).1 ++ (sigmaW n a b c d).2) :
    ∃ m k i, p = Zx n m k i ∧ k ≠ i ∧ m < 2 ^ n ∧ k < 2 ^ n ∧ i < 2 ^ n := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  simp only [sigmaW, List.mem_append, or_assoc] at hp
  rcases hp with h | h | h | h | h | h | h | h <;> obtain ⟨rfl, hne⟩ := mem_L h <;>
    exact ⟨_, _, _, rfl, hne, by repeat' (first | apply tau_lt | omega),
      by repeat' (first | apply tau_lt | omega), by repeat' (first | apply tau_lt | omega)⟩

theorem patt_0132 (hn : 2 ≤ n) : patt n 0 1 3 2 = some (2, 1, 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold patt
  rw [show m + 2 = 2 + m by omega, List.range_add, List.findSome?_append]
  rfl

/-- The gadget of Definition 8.3: the multi-controlled `H` with its box on wire `1`,
its `H` on wire `0` and white controls above. -/
def gadget (n : ℕ) : Circ n :=
  colour n (placeAt2 n (stdMch n) 0 1) (fun _ => 0) (fun j => j < 2)

theorem dec_0132 (hn : 3 ≤ n) : dec n (Hh n 0 1 3 2) = gadget n := by
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [dec_Hh (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    if_pos (by unfold Distinct4; omega)]
  simp only [dHH4, patt_0132 (by omega : 2 ≤ n)]
  simp only [show ¬ (2 = 1) by omega, if_false, gadget, colour]
  have hf : (List.range n).filter (fun j => !(j == 1 || j == 0) && bitOf (gray 0) j == 0) =
      (List.range n).filter (fun j => !decide (j < 2) && 0 == 0) := by
    apply List.filter_congr
    intro j _
    have h0 : bitOf (gray 0) j = 0 := by simp [bitOf, gray]
    rw [h0]
    rcases j with _ | _ | j <;> simp
  rw [hf]

/-- (35) decodes by definition. -/
theorem dec35 (hn : 3 ≤ n) (a b c d : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hc : c < 2 ^ n)
    (hd : d < 2 ^ n) (h : Distinct4 a b c d) (hp : patt n a b c d = none) :
    decW n (wordOf [Hh n a b c d]) =
      decW n (wordOf ((sigmaW n a b c d).1 ++ [Hh n 0 1 3 2] ++ (sigmaW n a b c d).2)) := by
  have hab : a ≠ b := h.1
  have hcd : c ≠ d := h.2.2.2.2.2
  rw [decW_wordOf, decW_wordOf, List.map_append, List.map_append, List.prod_append,
    List.prod_append]
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one, dec_Hh ha hb hc hd hab hcd,
    if_pos h, dHH4, hp, dec_0132 hn]
  rw [drawn_three]
  simp only [drawn, List.reverse_reverse, mul_assoc]
  have hmem := sigma_mem hn ha hb hc hd
  congr 2
  · apply List.map_congr_left
    intro p hp'
    obtain ⟨m, k, i, rfl, hki, hm, hk, hi⟩ := hmem p (List.mem_append_left _ hp')
    simp [dec, Zx, ix_ne hk hi hki]
  · congr 1
    apply List.map_congr_left
    intro p hp'
    obtain ⟨m, k, i, rfl, hki, hm, hk, hi⟩ := hmem p (List.mem_append_right _ hp')
    simp [dec, Zx, ix_ne hk hi hki]

end QCert.RealCliffordCH.Sec8.E
