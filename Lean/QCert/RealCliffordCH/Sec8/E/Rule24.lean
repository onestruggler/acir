/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (24)

`D((-1)_[a]X_[a,a+1])` and `D((-1)_[a+1]X_[a+1,a+2])` are the multi-controlled
`(-1)^{¬α} ZX` on the wire `t` where the Gray code changes at `a` and the
`(-1)^{¬β} ZX` on the wire `t'` where it changes at `a + 1` (`t ≠ t'`), each
controlled by the other's target (of colours `β`, `¬α`) and by the same
colours `x` on the other wires.  In the frame of the wires `t, t'` the rule is
the braid relation of the canonical gates `g24a N α β x` (target `0`) and
`g24b N α β x` (target `1`), which is (358) when `α = 0`, `β = 1` and `x` is all
black (`canon24`, as in the paper):

* the colours `x` by (81) (`X` on a control on both sides);
* `α` by `X` on wire `0`: on the control of `g24b` that is (81), on the target
  of `g24a` it exchanges `ZX` and `XZ` (`tflip0`, from (356) and (81));
* `β` by `X` on wire `1`, the same with the roles exchanged (`tflip1`, `tflip0`
  conjugated by the swap of the wires `0, 1`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule32

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Conjugating by involutions -/

section Conj

variable {N : ℕ}

theorem drawn3 (a b c : Circ N) : drawn [a, b, c] = c * b * a := by simp [drawn, mul_assoc]

/-- The braid relation `a b a = b a b`. -/
def Braid (a b : Circ N) : Prop := Derivable (theory N) (drawn [a, b, a]) (drawn [b, a, b])

/-- Conjugating a braid relation by an involution. -/
theorem Braid.conj {a b a' b' u : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (ha : Derivable (theory N) (u * a * u) a') (hb : Derivable (theory N) (u * b * u) b')
    (h : Braid a b) : Braid a' b' := by
  unfold Braid at *
  have e : ∀ x y : Circ N, drawn [x, y, x] = x * (y * x) := by intro x y; simp [drawn]
  rw [e a b, e b a] at h
  rw [e a' b', e b' a']
  have k : ∀ x y x' y' : Circ N, Derivable (theory N) (u * x * u) x' →
      Derivable (theory N) (u * y * u) y' →
      Derivable (theory N) (u * (x * (y * x)) * u) (x' * (y' * x')) := by
    intro x y x' y' hx hy
    exact (conj_mul hu).trans (dmul hx ((conj_mul hu).trans (dmul hy hx)))
  exact (k a b a' b' ha hb).symm.trans ((dctx u u h).trans (k b a b' a' hb ha))

theorem Braid.congr {a b a' b' : Circ N} (ha : a = a') (hb : b = b') (h : Braid a b) :
    Braid a' b' := by
  subst ha hb; exact h

/-- `X` on wire `q` commutes with a row of `X` gates on other wires. -/
theorem x_comm_xs (q : ℕ) : ∀ (ws : List ℕ), q ∉ ws →
    Derivable (theory N) (xAt N q * drawn (ws.map (xAt N))) (drawn (ws.map (xAt N)) * xAt N q)
  | [], _ => by simp only [List.map_nil, drawn, List.reverse_nil, List.prod_nil, mul_one, one_mul]
                exact Derivable.refl _
  | w :: ws, h => by
    have hw : q ≠ w := fun e => h (by simp [e])
    have ih := x_comm_xs q ws (fun h' => h (by simp [h']))
    rw [List.map_cons, Net.drawn_cons, ← mul_assoc]
    refine (dright _ ih).trans ?_
    rw [mul_assoc, mul_assoc]
    exact dleft _ (D.xAt_comm N q w hw)

end Conj

/-! ## `X` on the target exchanges `ZX` and `XZ` -/

theorem sgnZX_kindSp (γ : Bool) : kindSp (Kind.sgnZX γ) = 1 := by cases γ <;> rfl

/-- (356) with any colours: `X` on the target (wire `0`) on both sides of a
multi-controlled `(-1)^γ ZX` with a control on every other wire. -/
theorem tflip0 {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (γ : Bool) (c : ℕ → Option Bool)
    (hc0 : c 0 = none) (hc : ∀ j, 1 ≤ j → j < N → (c j).isSome) :
    Derivable (theory N) (drawn [xAt N 0, mc N (Kind.sgnZX γ) [0] c, xAt N 0])
      (mc N (Kind.sgnZX !γ) [0] c) := by
  set ws := whiteWires N [0] c with hws_def
  have hnd : ws.Nodup := whiteWires_nodup N [0] c
  have hmem : ∀ j ∈ ws, j < N ∧ j ∉ [0] ∧ blackOn 1 N j = some true := by
    intro j hj
    obtain ⟨h1, _, h3⟩ := MS.mem_whiteWires.1 hj
    refine ⟨h1, h3, ?_⟩
    have : j ≠ 0 := by simpa using h3
    simp only [blackOn]; split_ifs <;> first | rfl | (exfalso; omega)
  have recol : ∀ K, Derivable (theory N) (colourW N ws (mc N K [0] (blackOn 1 N))) (mc N K [0] c) := by
    intro K
    refine (D.N13.mc_colour N K [0] (blackOn 1 N) ws hnd hmem).trans
      (der_of_eq (Net.mc_congr N K [0] ?_))
    intro j hj
    by_cases hjw : j ∈ ws
    · simp only [if_pos hjw]; exact ((MS.mem_whiteWires.1 hjw).2.1).symm
    · simp only [if_neg hjw]
      rcases j with _ | j
      · simp [blackOn, hc0]
      · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hc (j + 1) (by omega) hj)
        cases b
        · exact absurd (MS.mem_whiteWires.2 ⟨hj, hb, by simp⟩) hjw
        · rw [hb]; simp only [blackOn]; split_ifs <;> first | rfl | (exfalso; omega)
  set Dw := drawn (ws.map (xAt N))
  have hx : Derivable (theory N) (xAt N 0 * Dw) (Dw * xAt N 0) :=
    x_comm_xs 0 ws (fun h => (hmem 0 h).2.1 (by simp))
  have conjD : ∀ A B : Circ N, Derivable (theory N) (xAt N 0 * A * xAt N 0) B →
      Derivable (theory N) (xAt N 0 * (Dw * A * Dw) * xAt N 0) (Dw * B * Dw) := by
    intro A B hAB
    have e1 : xAt N 0 * (Dw * A * Dw) * xAt N 0 = (xAt N 0 * Dw) * A * (Dw * xAt N 0) := by
      simp only [mul_assoc]
    have e2 : Dw * (xAt N 0 * A * xAt N 0) * Dw = (Dw * xAt N 0) * A * (xAt N 0 * Dw) := by
      simp only [mul_assoc]
    rw [e1]
    refine (dmul (dright A hx) hx.symm).trans ?_
    rw [← e2]
    exact dctx Dw Dw hAB
  have hxx := D.xx N 0 (by omega)
  have key : Derivable (theory N) (xAt N 0 * mc N (Kind.sgnZX γ) [0] (blackOn 1 N) * xAt N 0)
      (mc N (Kind.sgnZX !γ) [0] (blackOn 1 N)) := by
    have h356 := D.eq356 N hN ih
    rw [drawn3] at h356
    cases γ
    · exact h356
    · show Derivable (theory N) (xAt N 0 * mc N .xz [0] (blackOn 1 N) * xAt N 0)
        (mc N .zx [0] (blackOn 1 N))
      refine (dctx _ _ h356.symm).trans ?_
      have e : xAt N 0 * (xAt N 0 * mc N .zx [0] (blackOn 1 N) * xAt N 0) * xAt N 0 =
          (xAt N 0 * xAt N 0) * mc N .zx [0] (blackOn 1 N) * (xAt N 0 * xAt N 0) := by
        simp only [mul_assoc]
      rw [e]
      have := dmul (dright (mc N .zx [0] (blackOn 1 N)) hxx) hxx
      simpa only [one_mul, mul_one] using this
  have hA := recol (Kind.sgnZX γ)
  have hB := recol (Kind.sgnZX !γ)
  rw [Net.colourW_eq] at hA hB
  rw [drawn3]
  exact (dctx (xAt N 0) (xAt N 0) hA.symm).trans ((conjD _ _ key).trans hB)

/-- The same with the target on wire `1`: `tflip0` conjugated by the swap of the
wires `0, 1`. -/
theorem tflip1 {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (γ : Bool) (c : ℕ → Option Bool)
    (hc1 : c 1 = none) (hc : ∀ j, j ≠ 1 → j < N → (c j).isSome) :
    Derivable (theory N) (drawn [xAt N 1, mc N (Kind.sgnZX γ) [1] c, xAt N 1])
      (mc N (Kind.sgnZX !γ) [1] c) := by
  have hsw := mcSwapAll ih
  set S := swAt N 0
  have sw : ∀ δ, Derivable (theory N) (S * mc N (Kind.sgnZX δ) [0] (c ∘ Net.tau 0) * S)
      (mc N (Kind.sgnZX δ) [1] c) := by
    intro δ
    have := hsw 0 (by omega) (Kind.sgnZX δ) [0] (c ∘ Net.tau 0) (by simp [sgnZX_kindSp])
      (by simp) (by intro t ht; simp at ht; omega)
    have e1 : [0].map (Net.tau 0) = [1] := by simp [Net.tau]
    have e2 : (c ∘ Net.tau 0) ∘ Net.tau 0 = c := by funext q; simp [Net.tau_tau]
    rw [e1, e2, drawn3] at this
    exact this
  have hss : Derivable (theory N) (S * S) 1 := Net.swsw N 0 (by omega)
  have hx := Net.x_conj N 0 0 (by omega)
  rw [show Net.tau 0 0 = 1 by simp [Net.tau]] at hx
  have h0 := tflip0 hN ih γ (c ∘ Net.tau 0) (by simp [Net.tau, hc1]) (by
    intro j hj1 hjN
    simp only [Function.comp]
    apply hc
    · unfold Net.tau; split_ifs <;> omega
    · exact Net.tau_lt (by omega) hjN)
  rw [drawn3] at h0
  rw [drawn3]
  set M0 := mc N (Kind.sgnZX γ) [0] (c ∘ Net.tau 0)
  refine (dmul (dmul hx.symm (sw γ).symm) hx.symm).trans ?_
  -- `(S x S)(S M S)(S x S) = S (x M x) S`
  have e : S * xAt N 0 * S * (S * M0 * S) * (S * xAt N 0 * S) =
      S * xAt N 0 * (S * S) * M0 * (S * S) * xAt N 0 * S := by simp only [mul_assoc]
  rw [e]
  have h1 := dright S (dright (xAt N 0) (dright (S * S) (dright M0 (dleft (S * xAt N 0) hss))))
  have h2 := dright S (dright (xAt N 0) (dleft (S * xAt N 0 * M0) hss))
  simp only [mul_one] at h1 h2
  refine h1.trans (h2.trans ?_)
  have e2 : S * xAt N 0 * M0 * xAt N 0 * S = S * (xAt N 0 * M0 * xAt N 0) * S := by
    simp only [mul_assoc]
  rw [e2]
  exact (dctx S S h0).trans (sw (!γ))

/-! ## The canonical form of (24) -/

/-- The gate of target `0`. -/
def g24a (N : ℕ) (α β : Bool) (x : ℕ → Bool) : Circ N :=
  mc N (Kind.sgnZX !α) [0] (ctlOr (ctlAt 1 β) (colOn 2 N x))

/-- The gate of target `1`. -/
def g24b (N : ℕ) (α β : Bool) (x : ℕ → Bool) : Circ N :=
  mc N (Kind.sgnZX !β) [1] (ctlOr (ctlAt 0 !α) (colOn 2 N x))

/-- `x` with the colour of wire `w` exchanged. -/
def flipAt (x : ℕ → Bool) (w : ℕ) : ℕ → Bool := fun j => if j = w then !x j else x j

section Canon

variable {N : ℕ}

theorem g24_congr {α β : Bool} {x y : ℕ → Bool} (h : ∀ j, 2 ≤ j → j < N → x j = y j) :
    g24a N α β x = g24a N α β y ∧ g24b N α β x = g24b N α β y := by
  have hc : ∀ (i : ℕ) (b : Bool), ∀ j < N,
      ctlOr (ctlAt i b) (colOn 2 N x) j = ctlOr (ctlAt i b) (colOn 2 N y) j := by
    intro i b j hj
    simp only [ctlOr, colOn]
    by_cases h2 : 2 ≤ j ∧ j < N
    · rw [if_pos h2, if_pos h2, h j h2.1 h2.2]
    · rw [if_neg h2, if_neg h2]
  exact ⟨Net.mc_congr N _ [0] (hc 1 β), Net.mc_congr N _ [1] (hc 0 !α)⟩

theorem setCtl_flipAt {i : ℕ} (hi : i < 2) (b : Bool) (x : ℕ → Bool) {w : ℕ} (hw : 2 ≤ w)
    (hwN : w < N) :
    setCtl (ctlOr (ctlAt i b) (colOn 2 N x)) w (some !(x w)) =
      ctlOr (ctlAt i b) (colOn 2 N (flipAt x w)) := by
  funext j
  simp only [setCtl, ctlOr, ctlAt, colOn, flipAt]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

theorem setCtl_ctlAt {i : ℕ} (hi : i < 2) (b : Bool) (x : ℕ → Bool) :
    setCtl (ctlOr (ctlAt i b) (colOn 2 N x)) i (some !b) = ctlOr (ctlAt i (!b)) (colOn 2 N x) := by
  funext j
  simp only [setCtl, ctlOr, ctlAt]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem ctlOr_at (i : ℕ) (b : Bool) (x : ℕ → Bool) :
    ctlOr (ctlAt i b) (colOn 2 N x) i = some b := by
  simp [ctlOr, ctlAt]

theorem ctlOr_bulk (i : ℕ) (b : Bool) (x : ℕ → Bool) (hi : i < 2) {w : ℕ} (hw : 2 ≤ w)
    (hwN : w < N) : ctlOr (ctlAt i b) (colOn 2 N x) w = some (x w) := by
  simp only [ctlOr, ctlAt, colOn]
  split_ifs <;> first | rfl | (exfalso; omega)

variable (hN : 3 ≤ N) (ih : IH N)

/-- `X` on a bulk wire recolours it. -/
theorem braid_flip_bulk {α β : Bool} {x : ℕ → Bool} {w : ℕ} (hw : 2 ≤ w) (hwN : w < N)
    (h : Braid (g24a N α β x) (g24b N α β x)) :
    Braid (g24a N α β (flipAt x w)) (g24b N α β (flipAt x w)) := by
  refine Braid.conj (D.xx N w hwN) ?_ ?_ h
  · have := D.eq81 N (Kind.sgnZX !α) [0] (ctlOr (ctlAt 1 β) (colOn 2 N x)) w (x w) hwN
      (by simp; omega) (ctlOr_bulk 1 β x (by omega) hw hwN)
    rw [drawn3, setCtl_flipAt (by omega) β x hw hwN] at this
    exact this
  · have := D.eq81 N (Kind.sgnZX !β) [1] (ctlOr (ctlAt 0 !α) (colOn 2 N x)) w (x w) hwN
      (by simp; omega) (ctlOr_bulk 0 (!α) x (by omega) hw hwN)
    rw [drawn3, setCtl_flipAt (by omega) (!α) x hw hwN] at this
    exact this

include hN ih in
/-- `X` on wire `0` exchanges `α`. -/
theorem braid_flip_α {α β : Bool} {x : ℕ → Bool} (h : Braid (g24a N α β x) (g24b N α β x)) :
    Braid (g24a N (!α) β x) (g24b N (!α) β x) := by
  refine Braid.conj (D.xx N 0 (by omega)) ?_ ?_ h
  · have := tflip0 hN ih (!α) (ctlOr (ctlAt 1 β) (colOn 2 N x)) (by simp [ctlOr, ctlAt, colOn])
      (by
        intro j hj hjN
        simp only [ctlOr, ctlAt, colOn]
        split_ifs <;> first | rfl | (exfalso; omega))
    rw [drawn3] at this
    exact this
  · have := D.eq81 N (Kind.sgnZX !β) [1] (ctlOr (ctlAt 0 !α) (colOn 2 N x)) 0 (!α) (by omega)
      (by simp) (ctlOr_at 0 (!α) x)
    rw [drawn3, setCtl_ctlAt (by omega) (!α) x] at this
    exact this

include hN ih in
/-- `X` on wire `1` exchanges `β`. -/
theorem braid_flip_β {α β : Bool} {x : ℕ → Bool} (h : Braid (g24a N α β x) (g24b N α β x)) :
    Braid (g24a N α (!β) x) (g24b N α (!β) x) := by
  refine Braid.conj (D.xx N 1 (by omega)) ?_ ?_ h
  · have := D.eq81 N (Kind.sgnZX !α) [0] (ctlOr (ctlAt 1 β) (colOn 2 N x)) 1 β (by omega)
      (by simp) (ctlOr_at 1 β x)
    rw [drawn3, setCtl_ctlAt (by omega) β x] at this
    exact this
  · have := tflip1 hN ih (!β) (ctlOr (ctlAt 0 !α) (colOn 2 N x)) (by simp [ctlOr, ctlAt, colOn])
      (by
        intro j hj hjN
        simp only [ctlOr, ctlAt, colOn]
        split_ifs <;> first | rfl | (exfalso; omega))
    rw [drawn3] at this
    exact this

include hN ih in
/-- The canonical form of (24), from (358). -/
theorem canon24 (α β : Bool) (x : ℕ → Bool) : Braid (g24a N α β x) (g24b N α β x) := by
  have base : Braid (g24a N false true (fun _ => true)) (g24b N false true (fun _ => true)) := by
    have h := D.eq358 N hN ih
    refine Braid.congr ?_ ?_ h
    · exact Net.mc_congr N _ [0] (fun j hj => by
        simp only [ctlOr, ctlAt, colOn, blackOn]
        split_ifs <;> first | rfl | (exfalso; omega))
    · exact Net.mc_congr N _ [1] (fun j hj => by
        simp only [ctlOr, ctlAt, colOn, blackOn]
        split_ifs <;> first | rfl | (exfalso; omega))
  have bulk : ∀ k, ∀ y : ℕ → Bool, (∀ j, k ≤ j → j < N → y j = true) →
      Braid (g24a N false true y) (g24b N false true y) := by
    intro k
    induction k with
    | zero =>
      intro y hy
      have := g24_congr (N := N) (α := false) (β := true) (x := fun _ => true) (y := y)
        (fun j _ hjN => (hy j (Nat.zero_le _) hjN).symm)
      exact Braid.congr this.1 this.2 base
    | succ k ihk =>
      intro y hy
      by_cases hk : k < N ∧ y k = false
      · have hy' : ∀ j, k ≤ j → j < N → flipAt y k j = true := by
          intro j hkj hjN
          simp only [flipAt]
          by_cases hj : j = k
          · subst hj; rw [if_pos rfl, hk.2]; rfl
          · rw [if_neg hj]; exact hy j (by omega) hjN
        have h' := ihk _ hy'
        have hback : flipAt (flipAt y k) k = y := by
          funext j; simp only [flipAt]; by_cases hj : j = k
          · subst hj; simp
          · simp [hj]
        by_cases h2 : 2 ≤ k
        · have := braid_flip_bulk h2 hk.1 h'
          rwa [hback] at this
        · have := g24_congr (N := N) (α := false) (β := true) (x := flipAt y k) (y := y)
            (fun j hj _ => by simp only [flipAt]; split_ifs <;> first | rfl | (exfalso; omega))
          exact Braid.congr this.1 this.2 h'
      · exact ihk y (fun j hkj hjN => by
          by_cases hj : j = k
          · subst hj
            cases hyk : y j
            · exact absurd ⟨hjN, hyk⟩ hk
            · rfl
          · exact hy j (by omega) hjN)
  have hx := bulk N x (fun j h1 h2 => absurd h2 (by omega))
  have hα : Braid (g24a N α true x) (g24b N α true x) := by
    cases α
    · exact hx
    · have := braid_flip_α hN ih hx
      exact this
  cases β
  · have := braid_flip_β hN ih hα
    exact this
  · exact hα

end Canon

/-! ## The rule -/

theorem tOf_succ_ne {n a : ℕ} (ha : a + 2 < 2 ^ n) : tOf n a ≠ tOf n (a + 1) := by
  obtain ⟨β, hβ, hs⟩ := succ_spec a
  obtain ⟨β', hβ', _⟩ := succ_spec (a + 1)
  rw [tOf_eq hβ (by omega), tOf_eq hβ' (by omega)]
  intro e
  subst e
  have h1 := hs β
  rw [hβ.2, hβ'.2] at h1
  simp at h1

theorem dec_bit (v i : ℕ) : decide (bitOf v i = 1) = v.testBit i := by
  rw [bitOf_eq]; cases v.testBit i <;> rfl

theorem kindZX_zero (n a : ℕ) :
    kindZX n a 0 = Kind.sgnZX (!(gray a).testBit (tOf n a)) := by
  unfold kindZX Kind.sgnZX
  rw [bitOf_eq]
  cases (gray a).testBit (tOf n a) <;> simp

/-- (24) decodes to (358). -/
theorem dec24 {M : ℕ} (ih : IH (M + 3)) (a : ℕ) (ha : a + 2 < 2 ^ (M + 3)) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf [Zx (M + 3) a a (a + 1), Zx (M + 3) (a + 1) (a + 1) (a + 2),
        Zx (M + 3) a a (a + 1)]))
      (decW (M + 3) (wordOf [Zx (M + 3) (a + 1) (a + 1) (a + 2), Zx (M + 3) a a (a + 1),
        Zx (M + 3) (a + 1) (a + 1) (a + 2)])) := by
  have e1 := dec_Zx_lo (n := M + 3) (a := a + 1) (by omega)
  rw [show a + 1 + 1 = a + 2 from rfl] at e1
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx_lo (show a + 1 < 2 ^ (M + 3) by omega), e1]
  rw [dZX1_mc (M + 2), dZX1_mc (M + 2), kindZX_zero, kindZX_zero]
  set N := M + 2 + 1
  set ta := tOf N a with hta
  set tb := tOf N (a + 1) with htb
  have hta' : ta < N := tOf_lt a (by omega)
  have htb' : tb < N := tOf_lt (a + 1) (by omega)
  have hne : ta ≠ tb := tOf_succ_ne (n := N) ha
  have hg1 : gray (a + 1) = gray a ^^^ 2 ^ ta := gray_succ_tOf (n := N) (a := a) (by omega)
  set α := (gray a).testBit ta
  set β := (gray a).testBit tb
  set x := pull2 ta tb (gray a)
  have hβ1 : (gray (a + 1)).testBit tb = β := by rw [hg1, testBit_xor_pow_ne (Ne.symm hne)]
  have hα1 : (gray (a + 1)).testBit ta = !α := by rw [hg1, testBit_xor_pow_self]
  have hnd : [ta, tb].Nodup := by simp [hne]
  have hps : ∀ p ∈ [ta, tb], p < N := by simp [hta', htb']
  rw [hβ1]
  set A := mc N (Kind.sgnZX !α) [ta] (ctlOf (gray a) ta)
  set B := mc N (Kind.sgnZX !β) [tb] (ctlOf (gray (a + 1)) tb)
  have fA : Derivable (theory N) (placedBy N (netOf [ta, tb]) (g24a N α β x)) A := by
    have := (frame2_one ih (Kind.sgnZX !α) (sgnZX_kindSp _) hta' htb' hne (gray a)).1
    rw [dec_bit] at this
    exact this
  have fB : Derivable (theory N) (placedBy N (netOf [ta, tb]) (g24b N α β x)) B := by
    have := (frame2_one ih (Kind.sgnZX !β) (sgnZX_kindSp _) htb' hta'
      (Ne.symm hne) (gray (a + 1))).2
    refine Derivable.trans (der_of_eq ?_) this
    unfold g24b
    congr 1
    refine Net.mc_congr N _ [1] (fun j hj => ?_)
    rw [dec_bit, hα1]
    rcases j with _ | _ | j
    · simp [ctlOr, ctlAt]
    · simp [ctlOr, ctlAt, colOn]
    · rw [ctlOr_bulk 0 _ _ (by omega) (by omega) hj, ctlOr_bulk 0 _ _ (by omega) (by omega) hj]
      simp only [Option.some.injEq, x, pull2, dec_bit]
      have h0 : frm [ta, tb] 0 = ta := frm_getD hnd hps (by simp)
      have hj0 : frm [ta, tb] (j + 1 + 1) ≠ ta := by
        intro e; have := frm_injective _ (e.trans h0.symm); omega
      rw [hg1, testBit_xor_pow_ne hj0]
  have hc := canon24 (show 3 ≤ M + 2 + 1 by omega) ih α β x
  have := via_frame hnd hps (L := [A, B, A]) (R := [B, A, B])
    (List.Forall₂.cons fA (List.Forall₂.cons fB (List.Forall₂.cons fA List.Forall₂.nil)))
    (List.Forall₂.cons fB (List.Forall₂.cons fA (List.Forall₂.cons fB List.Forall₂.nil))) hc
  simpa [drawn, mul_assoc] using this

end QCert.RealCliffordCH.Sec8.E
