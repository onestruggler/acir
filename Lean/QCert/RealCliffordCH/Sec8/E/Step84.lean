/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.2: the step of Lemma 8.4, hence Lemma 8.4

The step of the induction of Appendix E.2: three boxes, on the wires `β`,
`t`, `β`, with the bit of the other wire flipped in the middle one and the
bit `t` flipped in the last, make the box on wire `t`.  At the canonical
position (`β = 0`, `t = 1`, `step84c`) this is the paper's chain:
(336) commutes the first two boxes, (309) merges the two boxes on wire `0`
into the box with wire `1` idle, (274) moves its box wire to wire `1`
(coloured by (81)), (309) on wire `1` splits it again and (311) cancels.
The equations on wire `1` are those on wire `0` conjugated by the swap of
the wires `0`, `1`.  The step at any two wires (`step84`) is the canonical
one moved by the network that brings `β`, `t` to `0`, `1` (`frame`), and
`lemma84` is Lemma 8.4.
-/
import QCert.RealCliffordCH.Sec8.E.Lemma84
import QCert.RealCliffordCH.Sec8.E.Transport

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Bits of `s xor 2^β` -/

theorem bitOf_xor_ne {s β j : ℕ} (h : j ≠ β) : bitOf (s ^^^ 2 ^ β) j = bitOf s j := by
  rw [bitOf_eq_bitOf, Nat.testBit_xor, Nat.testBit_two_pow_of_ne (Ne.symm h)]; simp

theorem bit_flip (s β : ℕ) : decide (bitOf (s ^^^ 2 ^ β) β = 1) = !decide (bitOf s β = 1) := by
  rw [bitOf_eq, bitOf_eq, Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases s.testBit β <;> rfl

/-! ## The canonical step -/

section Canonical

variable (N : ℕ) (x : ℕ → Bool)

/-- The box on wire `0` with the control `a` on wire `1` and `x` above. -/
abbrev B0 (a : Bool) : Circ N := mc N .box [0] (ctlOr (ctlAt 1 a) (colOn 2 N x))

/-- The box on wire `1` with the control `b` on wire `0` and `x` above. -/
abbrev B1 (b : Bool) : Circ N := mc N .box [1] (ctlOr (ctlAt 0 b) (colOn 2 N x))

variable {N}

theorem setCtl_one (a : Option Bool) :
    setCtl (colOn 1 N x) 1 a = ctlOr (fun j => if j = 1 then a else none) (colOn 2 N x) := by
  funext j
  by_cases h : j = 1
  · subst h; cases a <;> simp [setCtl, ctlOr, colOn]
  · simp only [setCtl, ctlOr, colOn, h, if_false, Option.none_or]
    by_cases h0 : j = 0
    · subst h0; simp
    · congr 1; apply propext; omega

theorem setCtl_one_some (a : Bool) : setCtl (colOn 1 N x) 1 (some a) = ctlOr (ctlAt 1 a) (colOn 2 N x) := by
  rw [setCtl_one]; rfl

theorem setCtl_one_none : setCtl (colOn 1 N x) 1 none = colOn 2 N x := by
  rw [setCtl_one]; funext j; simp [ctlOr]

theorem swap01_box (ih : IH N) (hN : 3 ≤ N) (c : ℕ → Option Bool) :
    Derivable (theory N) (placedBy N [0] (mc N .box [0] c)) (mc N .box [1] (c ∘ Net.tau 0)) := by
  have := placedBy_mc (mcSwapAll ih) [0] (fun j hj => by simp at hj; omega) .box [0] c rfl
    (by simp) (by simp; omega)
  simpa [pos_cons, Net.tau] using this

theorem flip01 (b : Bool) :
    ctlOr (fun j => if j = 1 then some b else none) (colOn 2 N x) ∘ Net.tau 0 =
      ctlOr (ctlAt 0 b) (colOn 2 N x) := by
  funext j
  rcases j with _ | _ | j <;> simp [ctlOr, ctlAt, colOn, Net.tau]

theorem flip01_none : colOn 2 N x ∘ Net.tau 0 = colOn 2 N x := by
  funext j
  rcases j with _ | _ | j <;> simp [colOn, Net.tau]

theorem conj01 (hN : 3 ≤ N) (l r : List (Circ N)) (h : Derivable (theory N) (drawn l) (drawn r)) :
    Derivable (theory N) (drawn (l.map (placedBy N [0]))) (drawn (r.map (placedBy N [0]))) :=
  frame_eq (N := N) (μ := [0]) (fun j hj => by simp at hj; omega) h

theorem drawn_mid {M : ℕ} (p q : List (Circ M)) {G G' : Circ M} (h : Derivable (theory M) G G') :
    Derivable (theory M) (drawn (p ++ [G] ++ q)) (drawn (p ++ [G'] ++ q)) := by
  rw [drawn_append, drawn_append, drawn_append, drawn_append, drawn_single, drawn_single]
  exact dleft _ (dright _ h)

/-- (309) on wire `1`: the boxes on wire `1` with the two colours on wire `0` merge. -/
theorem merge309_one (ih : IH N) (hN : 3 ≤ N) (b : Bool) :
    Derivable (theory N) (drawn [B1 N x b, B1 N x !b]) (mc N .box [1] (colOn 2 N x)) := by
  have h := D.eq309 N hN ih x 1 le_rfl (by omega) b
  have h' := conj01 hN [mc N .box [0] (setCtl (colOn 1 N x) 1 (some b)),
    mc N .box [0] (setCtl (colOn 1 N x) 1 (some !b))] [mc N .box [0] (setCtl (colOn 1 N x) 1 none)]
    (by rw [drawn_single]; exact h)
  simp only [List.map_cons, List.map_nil] at h'
  refine ((?_ : Derivable _ _ _).trans h').trans ?_
  · rw [drawn_two, drawn_two]
    refine dmul ?_ ?_
    · refine (?_ : Derivable _ _ _).symm
      have := swap01_box ih hN (setCtl (colOn 1 N x) 1 (some !b))
      rw [setCtl_one, flip01] at this; rw [setCtl_one]; exact this
    · refine (?_ : Derivable _ _ _).symm
      have := swap01_box ih hN (setCtl (colOn 1 N x) 1 (some b))
      rw [setCtl_one, flip01] at this; rw [setCtl_one]; exact this
  · rw [drawn_single]
    have := swap01_box ih hN (setCtl (colOn 1 N x) 1 none)
    rw [setCtl_one_none, flip01_none] at this; rw [setCtl_one_none]; exact this

/-- (311) on wire `1`. -/
theorem invol311_one (ih : IH N) (hN : 3 ≤ N) (b : Bool) :
    Derivable (theory N) (drawn [B1 N x b, B1 N x b]) 1 := by
  set y : ℕ → Bool := fun j => if j = 1 then b else x j
  have h := D.eq311 N hN ih y
  have hc : colOn 1 N y = ctlOr (fun j => if j = 1 then some b else none) (colOn 2 N x) := by
    funext j
    rcases j with _ | _ | j
    · simp [colOn, ctlOr]
    · simp [colOn, ctlOr, y]; omega
    · simp [colOn, ctlOr, y]
  rw [hc] at h
  have h' := conj01 hN [mc N .box [0] (ctlOr (fun j => if j = 1 then some b else none) (colOn 2 N x)),
    mc N .box [0] (ctlOr (fun j => if j = 1 then some b else none) (colOn 2 N x))] []
    (by simpa [drawn] using h)
  simp only [List.map_cons, List.map_nil] at h'
  refine (?_ : Derivable _ _ _).trans (h'.trans (by
    simp only [drawn, List.reverse_nil, List.prod_nil]; exact Derivable.refl _))
  rw [drawn_two, drawn_two]
  have := swap01_box ih hN (ctlOr (fun j => if j = 1 then some b else none) (colOn 2 N x))
  rw [flip01] at this
  exact dmul this.symm this.symm

/-- The white wires of `x` above wire `1`. -/
def whitesAbove (N : ℕ) (x : ℕ → Bool) : List ℕ := (List.range N).filter fun j => 2 ≤ j && !x j

theorem flipOn_whites (K : Kind) :
    flipOn (whitesAbove N x) (blackOn 2 N) = colOn 2 N x := by
  funext j
  simp only [flipOn, whitesAbove, List.mem_filter, List.mem_range, blackOn, colOn]
  by_cases h : 2 ≤ j ∧ j < N
  · cases hx : x j <;> simp [h, hx, h.1]
  · simp only [h, if_false]
    split_ifs with h' <;> simp_all

/-- (274) coloured by (81): the box with wire `0` idle moves its box wire. -/
theorem move274 (ih : IH N) (hN : 3 ≤ N) :
    Derivable (theory N) (mc N .box [0] (colOn 2 N x)) (mc N .box [1] (colOn 2 N x)) := by
  have hw : ∀ (tg : List ℕ), (∀ t ∈ tg, t < 2) → ∀ j ∈ whitesAbove N x,
      j < N ∧ j ∉ tg ∧ (blackOn 2 N j).isSome := by
    intro tg htg j hj
    simp only [whitesAbove, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at hj
    refine ⟨hj.1, fun h => by have := htg j h; omega, by simp [blackOn, hj.1, hj.2.1]⟩
  have hnd : (whitesAbove N x).Nodup := (List.nodup_range).filter _
  have r0 := recolour .box [0] (whitesAbove N x) (blackOn 2 N) hnd (hw [0] (by simp))
  have r1 := recolour .box [1] (whitesAbove N x) (blackOn 2 N) hnd (hw [1] (by simp))
  rw [flipOn_whites x .box] at r0 r1
  exact r0.symm.trans ((drawn_mid _ _ (D.eq274 N hN ih).symm).trans r1)

/-- The step of Lemma 8.4 at the canonical position (`β = 0`, `t = 1`). -/
theorem step84c (ih : IH N) (hN : 3 ≤ N) (a b : Bool) :
    Derivable (theory N) (drawn [B0 N x a, B1 N x !b, B0 N x !a]) (B1 N x b) := by
  -- (336): the first two boxes commute
  have h1 : Derivable (theory N) (drawn [B0 N x a, B1 N x !b, B0 N x !a])
      (drawn [B1 N x !b, B0 N x a, B0 N x !a]) := by
    have this : Derivable (theory N) (drawn [B0 N x a, B1 N x !b]) (drawn [B1 N x !b, B0 N x a]) :=
      D.eq336 N hN ih x x a !b
    rw [drawn_two, drawn_two] at this
    rw [drawn_three, drawn_three]
    exact dleft _ this
  -- (309): the two boxes on wire `0` merge
  have h2 : Derivable (theory N) (drawn [B0 N x a, B0 N x !a]) (mc N .box [0] (colOn 2 N x)) := by
    have := D.eq309 N hN ih x 1 le_rfl (by omega) a
    rwa [setCtl_one_some, setCtl_one_some, setCtl_one_none] at this
  refine h1.trans ?_
  rw [drawn_three, ← mul_assoc, ← drawn_two (B0 N x a) (B0 N x !a)]
  have hm := merge309_one x ih hN (!b)
  rw [Bool.not_not] at hm
  refine (dright _ (h2.trans ((move274 x ih hN).trans hm.symm))).trans ?_
  rw [drawn_two, mul_assoc]
  have := invol311_one x ih hN !b
  rw [drawn_two] at this
  have := dleft (B1 N x b) this
  rwa [mul_one] at this

end Canonical

/-! ## The step at any two wires, and Lemma 8.4 -/

/-- The step of Lemma 8.4 at every pair of wires. -/
theorem step84 {n : ℕ} (ih : IH n) (hn : 3 ≤ n) : Step84 n := by
  intro β t s hβ ht hβt
  have hnd : [β, t].Nodup := by simp [hβt]
  have hps : ∀ p ∈ [β, t], p < n := by simp [hβ, ht]
  have hπ0 : frm [β, t] 0 = β := frm_getD hnd hps (by simp)
  have hπ1 : frm [β, t] 1 = t := frm_getD hnd hps (by simp)
  have hπ : ∀ j, 2 ≤ j → j < n → frm [β, t] j ≠ β ∧ frm [β, t] j ≠ t := by
    intro j hj _
    exact ⟨fun h => by have := frm_injective _ (h.trans hπ0.symm); omega,
      fun h => by have := frm_injective _ (h.trans hπ1.symm); omega⟩
  set π := frm [β, t]
  set x : ℕ → Bool := fun j => decide (bitOf s (π j) = 1)
  set a := decide (bitOf s t = 1)
  set b := decide (bitOf s β = 1)
  have hsw := mcSwapAll ih
  have hμ := netOf_ok hnd hps
  -- each box is the canonical one, moved
  have fr : ∀ (w : ℕ) (c : ℕ → Option Bool) (cc : ℕ → Option Bool), w < 2 →
      (∀ j < n, (c ∘ π) j = cc j) →
      Derivable (theory n) (placedBy n (netOf [β, t]) (mc n .box [w] cc)) (mc n .box [π w] c) := by
    intro w c cc hw hcc
    have := frame hsw hnd hps .box [w] c rfl (by simp) (by simp; omega)
    rw [Net.mc_congr n .box [w] (c := c ∘ frm [β, t]) (c' := cc) hcc] at this
    simpa using this
  have e1 : ∀ j < n, (ctlOf s β ∘ π) j = ctlOr (ctlAt 1 a) (colOn 2 n x) j := by
    intro j hj
    rcases j with _ | _ | j
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ0]
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ1, Ne.symm hβt, a]
    · have := hπ (j + 2) (by omega) hj
      simp [ctlOf, ctlOr, ctlAt, colOn, this.1, x, hj]
  have e2 : ∀ j < n, (ctlOf (s ^^^ 2 ^ β) t ∘ π) j = ctlOr (ctlAt 0 !b) (colOn 2 n x) j := by
    intro j hj
    rcases j with _ | _ | j
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ0, hβt, b, bit_flip]
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ1]
    · have := hπ (j + 2) (by omega) hj
      simp [ctlOf, ctlOr, ctlAt, colOn, this.2, x, hj, bitOf_xor_ne this.1]
  have e3 : ∀ j < n, (ctlOf (s ^^^ 2 ^ t) β ∘ π) j = ctlOr (ctlAt 1 !a) (colOn 2 n x) j := by
    intro j hj
    rcases j with _ | _ | j
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ0]
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ1, Ne.symm hβt, a, bit_flip]
    · have := hπ (j + 2) (by omega) hj
      simp [ctlOf, ctlOr, ctlAt, colOn, this.1, x, hj, bitOf_xor_ne this.2]
  have e4 : ∀ j < n, (ctlOf s t ∘ π) j = ctlOr (ctlAt 0 b) (colOn 2 n x) j := by
    intro j hj
    rcases j with _ | _ | j
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ0, hβt, b]
    · simp [ctlOf, ctlOr, ctlAt, colOn, hπ1]
    · have := hπ (j + 2) (by omega) hj
      simp [ctlOf, ctlOr, ctlAt, colOn, this.2, x, hj]
  have f1 := fr 0 (ctlOf s β) _ (by omega) e1
  have f2 := fr 1 (ctlOf (s ^^^ 2 ^ β) t) _ (by omega) e2
  have f3 := fr 0 (ctlOf (s ^^^ 2 ^ t) β) _ (by omega) e3
  have f4 := fr 1 (ctlOf s t) _ (by omega) e4
  rw [hπ0] at f1 f3
  rw [hπ1] at f2 f4
  have hc := frame_eq hμ (l := [B0 n x a, B1 n x !b, B0 n x !a]) (r := [B1 n x b])
    (by rw [drawn_single]; exact step84c x ih hn a b)
  simp only [List.map_cons, List.map_nil] at hc
  rw [drawn_three, drawn_single] at hc
  rw [drawn_three]
  exact ((dmul f3.symm (dmul f2.symm f1.symm)).trans hc).trans f4

theorem gInv_flip {n s t : ℕ} (hs : s < 2 ^ n) (ht : t < n) :
    gInv n (s ^^^ 2 ^ t) = gInv n s ^^^ msk t := by
  have hm : msk t < 2 ^ n := by
    have : 2 ^ (t + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) ht
    unfold msk; omega
  have hx : gInv n s ^^^ msk t < 2 ^ n := Nat.xor_lt_two_pow (gInv_lt hs) hm
  have : gray (gInv n s ^^^ msk t) = s ^^^ 2 ^ t := by rw [gray_pair, gray_gInv hs]
  rw [← this, gInv_gray hx]

/-- **Lemma 8.4.** For a state `s` with bit `t` clear (the bitstring `x0y`),
`D((-1)_[G⁻¹(x0y)](-1)_[G⁻¹(x1y)])` is the box on wire `t` controlled by the
other bits of `s`. -/
theorem lemma84 {k : ℕ} (ih : IH (k + 1)) (hn : 3 ≤ k + 1) {s t : ℕ} (hs : s < 2 ^ (k + 1))
    (ht : t < k + 1) (hst : s.testBit t = false) :
    Derivable (theory (k + 1)) (dZZ (k + 1) (gInv (k + 1) s) (gInv (k + 1) (s ^^^ 2 ^ t)))
      (boxAt (k + 1) t s) := by
  have hstep := step84 ih hn
  rw [gInv_flip hs ht]
  set p0 := gInv (k + 1) s
  have hp0 : p0 < 2 ^ (k + 1) := gInv_lt hs
  have hm : msk t < 2 ^ (k + 1) := by
    have : 2 ^ (t + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) ht
    unfold msk; omega
  have hq : p0 ^^^ msk t < 2 ^ (k + 1) := Nat.xor_lt_two_pow hp0 hm
  cases hb : p0.testBit t with
  | false =>
    have := lemma84_of hstep _ p0 t le_rfl hb hq
    rwa [gray_gInv hs] at this
  | true =>
    set p := p0 ^^^ msk t
    have hpb : p.testBit t = false := by
      rw [Nat.testBit_xor, testBit_msk, hb]; simp
    have hpp : p ^^^ msk t = p0 := by
      simp only [p, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have := lemma84_of hstep _ p t le_rfl hpb (by rw [hpp]; exact hp0)
    have e : boxAt (k + 1) t (s ^^^ 2 ^ t) = boxAt (k + 1) t s := by simp only [boxAt, ctlOf_flip]
    rw [hpp, gray_pair, gray_gInv hs, e] at this
    rw [dZZ_comm]
    exact this

end QCert.RealCliffordCH.Sec8.E
