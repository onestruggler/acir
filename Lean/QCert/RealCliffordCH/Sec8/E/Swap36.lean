/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4 and E.5: the decoded swap `D(E_{k,ℓ}(swap))`

`E_{k,ℓ}(swap)` (Definition 8.2, `encSwap`) is the encoding of `CZ` on the
wires `ℓ, ℓ + 1`, followed by three products over the bitstrings `x` above
and `y` below of mixed letters on pairs differing in one bit.  By Lemma 8.5
the letters of each product are multi-controlled `ZX` or `XZ` gates, which
merge by (354) (`decode_zx_list`): the `ZX` on wire `ℓ` controlled by wire
`ℓ + 1`, the `XZ` on wire `ℓ + 1` controlled by wire `ℓ`, the `ZX` again.  With
the decoded `CZ` (Lemma 8.6) this is the swap of the wires `ℓ, ℓ + 1`, by a
two-wire identity (Lemma 5.1).  Checked numerically first
(`gen/sec8/e/m36.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Lemma85
import QCert.RealCliffordCH.Sec8.E.Lemma87Gates

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

/-! ## A word of mixed letters on pairs differing in one bit -/

/-- The decoding of the word of the letters `(-1)_[G⁻¹(s_i xor 2^t)]X_[G⁻¹(s_i),G⁻¹(s_i xor 2^t)]`
(`up = true`) or `(-1)_[G⁻¹(s_i)]X_[…]` (`up = false`), `i < 2^|ws|`, the bits of `s_i` off
the wire `t` being the bits of `i` on the wires `ws` and `base` elsewhere, is the `ZX`
(resp. `XZ`) on wire `t` with the wires `ws` idle. -/
theorem decode_zx_list {M : ℕ} (ih : IH (M + 3)) (up : Bool) {t : ℕ} (ht : t < M + 3)
    (ws : List ℕ) (hnd : ws.Nodup) (htw : t ∉ ws) (hws : ∀ w ∈ ws, w < M + 3)
    (base : ℕ → Option Bool) (hb : base t = none) (sOf : ℕ → ℕ)
    (hs : ∀ i < 2 ^ ws.length, sOf i < 2 ^ (M + 3) ∧ (sOf i).testBit t = false ∧
      ∀ j < M + 3, ctlOf (sOf i) t j = bitsOn ws i base j) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf ((List.range (2 ^ ws.length)).map fun i =>
        PG.zx (gx (M + 3) (if up then sOf i ^^^ 2 ^ t else sOf i)) (gx (M + 3) (sOf i))
          (gx (M + 3) (sOf i ^^^ 2 ^ t)))))
      (mc (M + 3) (Kind.sgnZX !up) [t] (idleOn ws base)) := by
  rw [decW_wordOf, List.map_map]
  have hm := mergeListGen (N := M + 3) (Kind.sgnZX !up) [t] (fun c hc w hw hwN b =>
      mergeAtZ ih (!up) ht c (hc t (by simp)) (w := w) (by simpa using hw) hwN b)
    ws base hnd (fun t' ht' => by simp at ht'; subst ht'; exact htw) hws (by simpa using hb)
  refine Derivable.trans ?_ hm
  apply prod_map_congr
  intro i hi
  obtain ⟨hsn, hst, hc⟩ := hs i (List.mem_range.1 hi)
  have h2t : 2 ^ t < 2 ^ (M + 3) := Nat.pow_lt_pow_right (by norm_num) ht
  have hs' : sOf i ^^^ 2 ^ t < 2 ^ (M + 3) := Nat.xor_lt_two_pow hsn h2t
  have hne : gx (M + 3) (sOf i) ≠ gx (M + 3) (sOf i ^^^ 2 ^ t) := by
    intro e
    have e' := congrArg Fin.val e
    rw [gx_val hsn, gx_val hs', gInv_flip hsn ht] at e'
    have hm0 : msk t ≠ 0 := by unfold msk; have := Nat.one_le_two_pow (n := t + 1); omega
    apply hm0
    have := congrArg (fun z => gInv (M + 3) (sOf i) ^^^ z) e'
    simp only [Nat.xor_self, ← Nat.xor_assoc, Nat.zero_xor] at this
    exact this.symm
  have L := lemma85 ih hsn ht hst
  show Derivable _ (dec (M + 3) (PG.zx _ _ _)) _
  simp only [dec, if_neg hne]
  cases up
  · simp only [Bool.false_eq_true, if_false, gx_val hsn, gx_val hs', Bool.not_false]
    refine L.1.trans (der_of_eq ?_)
    rw [Net.mc_congr _ _ [t] hc]; rfl
  · simp only [if_true, gx_val hsn, gx_val hs', Bool.not_true]
    refine L.2.trans (der_of_eq ?_)
    rw [Net.mc_congr _ _ [t] hc]; rfl

/-! ## Two-wire circuits placed on the wires `ℓ, ℓ + 1` -/

section Two

variable {N : ℕ}

theorem placeG_mul2 {ℓ : ℕ} (hℓ : ℓ + 2 ≤ N) (a b : Circ 2) :
    Derivable (theory N) (placeG N (a * b) [ℓ, ℓ + 1]) (placeG N a [ℓ, ℓ + 1] * placeG N b [ℓ, ℓ + 1]) := by
  rw [placeG_eq, placeG_eq, placeG_eq, atBot_mul]
  exact Net.placedBy_mul _ (netK_spec (ps := [ℓ, ℓ + 1]) (by simp)
    (by intro p hp; simp at hp; omega) 2 le_rfl).1 _ _

theorem placeG_der2 {ℓ : ℕ} (hℓ : ℓ + 2 ≤ N) {a b : Circ 2} (h : Derivable (theory 2) a b) :
    Derivable (theory N) (placeG N a [ℓ, ℓ + 1]) (placeG N b [ℓ, ℓ + 1]) := by
  rw [placeG_eq, placeG_eq]
  exact placedBy_cong _ (der_atBot h N (by omega))

end Two

/-- The two-wire identity: `CZ · ZX · (swap XZ swap) · ZX` is the swap. -/
theorem two_swap (ih2 : CompleteAt 2) :
    Derivable (theory 2) ((cz : Circ 2) * zx 1 * (swap * xz 1 * swap) * zx 1) swap :=
  ih2 _ _ (Fast.sem_of_fast (by decide +kernel))

/-! ## The decoded swap -/

section Swap

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- The first and third products of `E_{k,ℓ}(swap)`: the `ZX` on wire `ℓ` controlled by `ℓ + 1`. -/
theorem dec_swapA (k ℓ : ℕ) (hk : k + ℓ + 2 = M + 3) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2)))))
      (mc (M + 3) .zx [ℓ] (blackL [ℓ + 1])) := by
  set ws := lowHigh ℓ 2 k with hws_def
  have hlen : ws.length = ℓ + k := lowHigh_length ℓ 2 k
  set sOf : ℕ → ℕ := fun i => i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 2 * 2 ^ ℓ + i % 2 ^ ℓ with hsOf
  have hmid : ∀ i q, (sOf i).testBit q =
      if q < ℓ then (i % 2 ^ ℓ).testBit q else if q < ℓ + 2 then (2 : ℕ).testBit (q - ℓ)
        else (i / 2 ^ ℓ).testBit (q - (ℓ + 2)) := fun i q =>
    testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) (by norm_num)
  have hbt : ∀ i, (sOf i).testBit ℓ = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), Nat.sub_self]; decide
  have hbt1 : ∀ i, (sOf i).testBit (ℓ + 1) = true := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), show ℓ + 1 - ℓ = 1 by omega]; decide
  have hl : ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) =
      (List.range (2 ^ ws.length)).map fun i =>
        PG.zx (gx (M + 3) (if true then sOf i ^^^ 2 ^ ℓ else sOf i)) (gx (M + 3) (sOf i))
          (gx (M + 3) (sOf i ^^^ 2 ^ ℓ)) := by
    simp only [grid_eq, List.map_map, if_true]
    rw [hlen, show (2 : ℕ) ^ (ℓ + k) = 2 ^ k * 2 ^ ℓ by rw [pow_add, mul_comm]]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    have e1 : i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + i % 2 ^ ℓ = sOf i := by
      simp only [hsOf]; ring
    have e2 : i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + i % 2 ^ ℓ = sOf i ^^^ 2 ^ ℓ := by
      rw [← add_two_pow_eq_xor (hbt i)]; simp only [hsOf]; ring
    rw [e1, e2]
  rw [hl]
  have hb : blackL [ℓ + 1] ℓ = none := by simp [blackL]
  have hnone : ∀ w ∈ ws, blackL [ℓ + 1] w = none := by
    intro w hw
    rw [hws_def, mem_lowHigh] at hw
    simp [blackL]; omega
  have hd := decode_zx_list ih true (t := ℓ) (by omega) ws (lowHigh_nodup ℓ 2 k)
    (by rw [hws_def, mem_lowHigh]; omega) (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega)
    (blackL [ℓ + 1]) hb sOf (by
      intro i hi
      refine ⟨?_, hbt i, ?_⟩
      · have := state_lt i 2 ℓ 2 k (by rw [hlen] at hi; exact hi) (by norm_num)
        rw [← hk, show k + ℓ + 2 = ℓ + 2 + k by omega]; exact this
      · apply ctlOf_eq_bitsOn ws (lowHigh_nodup ℓ 2 k) _ ℓ (sOf i) i
          (by rw [hws_def, mem_lowHigh]; omega)
        · intro r hr
          rw [hlen] at hr
          exact testBit_state i 2 ℓ 2 k r hr (by norm_num)
        · intro j hj hjw
          rw [hws_def, mem_lowHigh] at hjw
          have : j = ℓ ∨ j = ℓ + 1 := by omega
          rcases this with rfl | rfl
          · simp [ctlOf, blackL]
          · simp [ctlOf, blackL, bitOf_eq, hbt1])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd

/-- The second product of `E_{k,ℓ}(swap)`: the `XZ` on wire `ℓ + 1` controlled by `ℓ`. -/
theorem dec_swapB (k ℓ : ℕ) (hk : k + ℓ + 2 = M + 3) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2)))))
      (mc (M + 3) .xz [ℓ + 1] (blackL [ℓ])) := by
  set ws := lowHigh ℓ 2 k with hws_def
  have hlen : ws.length = ℓ + k := lowHigh_length ℓ 2 k
  set sOf : ℕ → ℕ := fun i => i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 1 * 2 ^ ℓ + i % 2 ^ ℓ with hsOf
  have hmid : ∀ i q, (sOf i).testBit q =
      if q < ℓ then (i % 2 ^ ℓ).testBit q else if q < ℓ + 2 then (1 : ℕ).testBit (q - ℓ)
        else (i / 2 ^ ℓ).testBit (q - (ℓ + 2)) := fun i q =>
    testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) (by norm_num)
  have hbt : ∀ i, (sOf i).testBit (ℓ + 1) = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), show ℓ + 1 - ℓ = 1 by omega]; decide
  have hbt0 : ∀ i, (sOf i).testBit ℓ = true := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega), Nat.sub_self]; decide
  have hl : ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) =
      (List.range (2 ^ ws.length)).map fun i =>
        PG.zx (gx (M + 3) (if false then sOf i ^^^ 2 ^ (ℓ + 1) else sOf i)) (gx (M + 3) (sOf i))
          (gx (M + 3) (sOf i ^^^ 2 ^ (ℓ + 1))) := by
    simp only [grid_eq, List.map_map, Bool.false_eq_true, if_false]
    rw [hlen, show (2 : ℕ) ^ (ℓ + k) = 2 ^ k * 2 ^ ℓ by rw [pow_add, mul_comm]]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    have e1 : i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + i % 2 ^ ℓ = sOf i := by
      simp only [hsOf]; ring
    have e2 : i / 2 ^ ℓ * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + i % 2 ^ ℓ =
        sOf i ^^^ 2 ^ (ℓ + 1) := by
      rw [← add_two_pow_eq_xor (hbt i)]; simp only [hsOf]; ring
    rw [e1, e2]
  rw [hl]
  have hb : blackL [ℓ] (ℓ + 1) = none := by simp [blackL]
  have hnone : ∀ w ∈ ws, blackL [ℓ] w = none := by
    intro w hw
    rw [hws_def, mem_lowHigh] at hw
    simp [blackL]; omega
  have hd := decode_zx_list ih false (t := ℓ + 1) (by omega) ws (lowHigh_nodup ℓ 2 k)
    (by rw [hws_def, mem_lowHigh]; omega) (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega)
    (blackL [ℓ]) hb sOf (by
      intro i hi
      refine ⟨?_, hbt i, ?_⟩
      · have := state_lt i 1 ℓ 2 k (by rw [hlen] at hi; exact hi) (by norm_num)
        rw [← hk, show k + ℓ + 2 = ℓ + 2 + k by omega]; exact this
      · apply ctlOf_eq_bitsOn ws (lowHigh_nodup ℓ 2 k) _ (ℓ + 1) (sOf i) i
          (by rw [hws_def, mem_lowHigh]; omega)
        · intro r hr
          rw [hlen] at hr
          exact testBit_state i 1 ℓ 2 k r hr (by norm_num)
        · intro j hj hjw
          rw [hws_def, mem_lowHigh] at hjw
          have : j = ℓ ∨ j = ℓ + 1 := by omega
          rcases this with rfl | rfl
          · simp [ctlOf, blackL, bitOf_eq, hbt0]
          · simp [ctlOf, blackL])
  rw [idleOn_of_none ws _ hnone] at hd
  exact hd

end Swap

theorem decW_append {n : ℕ} (l₁ l₂ : List (PG (2 ^ n))) :
    decW n (wordOf (l₁ ++ l₂)) = decW n (wordOf l₁) * decW n (wordOf l₂) := by
  simp [decW_wordOf, List.map_append, List.prod_append]

section Swap2

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- The decoded `CZ` of `E_{k,ℓ}(swap)` (Lemma 8.6). -/
theorem dec_swapCZ (k ℓ : ℕ) (hk : k + ℓ + 2 = M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (enc2 (M + 3) .CZ k ℓ)))
      (place2 (M + 3) ℓ cz) := by
  have e : enc2 (M + 3) .CZ k ℓ = encL (M + 3) (.C ℓ) := by
    rw [show k = M + 3 - 2 - ℓ by omega]; rfl
  rw [e]
  rcases ℓ with _ | ℓ
  · exact lemma86_CZ_lo ih
  · exact lemma86_CZ_hi ih ℓ (by omega)

/-- **The decoded swap.** `D(E_{k,ℓ}(swap))` is the swap of the wires `ℓ, ℓ + 1`. -/
theorem dec_encSwap (k ℓ : ℕ) (hk : k + ℓ + 2 = M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encSwap (M + 3) k ℓ))) (swAt (M + 3) ℓ) := by
  have hℓ : ℓ + 2 ≤ M + 3 := by omega
  have e : encSwap (M + 3) k ℓ = enc2 (M + 3) .CZ k ℓ ++
      ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) ++
      ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 0 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) ++
      ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 2) + 1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) := rfl
  rw [e, decW_append, decW_append, decW_append]
  refine (dmul (dmul (dmul (dec_swapCZ ih k ℓ hk) (dec_swapA ih k ℓ hk)) (dec_swapB ih k ℓ hk))
    (dec_swapA ih k ℓ hk)).trans ?_
  -- everything placed on `[ℓ, ℓ + 1]`
  have hZX : mc (M + 3) .zx [ℓ] (blackL [ℓ + 1]) = placeG (M + 3) (zx 1) [ℓ, ℓ + 1] := by
    rw [mc_black .zx (by simp) (by simp; omega) (by simp)]; rfl
  have hXZ0 : mc (M + 3) .xz [ℓ + 1] (blackL [ℓ]) = placeG (M + 3) (xz 1) [ℓ + 1, ℓ] := by
    rw [mc_black .xz (by simp) (by simp; omega) (by simp)]; rfl
  have hsw := placeG_swap (N := M + 3) (xz 1 : Circ 2) (ps := [ℓ, ℓ + 1]) (by simp)
    (by intro p hp; simp at hp; omega) rfl ℓ hℓ
  rw [show [ℓ, ℓ + 1].map (Net.tau ℓ) = [ℓ + 1, ℓ] by simp [Net.tau]] at hsw
  have hS : Derivable (theory (M + 3)) (swAt (M + 3) ℓ) (placeG (M + 3) swap [ℓ, ℓ + 1]) :=
    place2_placeG swap (M + 3) ℓ hℓ
  have hXZ : Derivable (theory (M + 3)) (mc (M + 3) .xz [ℓ + 1] (blackL [ℓ]))
      (placeG (M + 3) (swap * xz 1 * swap) [ℓ, ℓ + 1]) := by
    rw [hXZ0]
    refine hsw.symm.trans ?_
    rw [D.N15.conj3]
    refine (dmul (dmul hS (Derivable.refl _)) hS).trans ?_
    exact ((placeG_mul2 hℓ ((swap : Circ 2) * xz 1) swap).trans
      (dright _ (placeG_mul2 hℓ (swap : Circ 2) (xz 1)))).symm
  have hCZ : Derivable (theory (M + 3)) (place2 (M + 3) ℓ cz) (placeG (M + 3) cz [ℓ, ℓ + 1]) :=
    place2_placeG cz (M + 3) ℓ hℓ
  rw [hZX]
  refine (dmul (dmul (dmul hCZ (Derivable.refl _)) hXZ) (Derivable.refl _)).trans ?_
  refine (dright _ (dright _ (placeG_mul2 hℓ (cz : Circ 2) (zx 1)).symm)).trans ?_
  refine (dright _ (placeG_mul2 hℓ ((cz : Circ 2) * zx 1) (swap * xz 1 * swap)).symm).trans ?_
  refine (placeG_mul2 hℓ ((cz : Circ 2) * zx 1 * (swap * xz 1 * swap)) (zx 1)).symm.trans ?_
  exact (placeG_der2 hℓ (two_swap (ih 2 (by omega)))).trans hS.symm

omit ih in
/-- The single-qubit identity `Z · ZX = X`. -/
theorem one_x (ih1 : CompleteAt 1) : Derivable (theory 1) ((z : Circ 1) * zx 0) x :=
  ih1 _ _ (Fast.sem_of_fast (by decide +kernel))

omit ih in
theorem mc_none_zx (ℓ : ℕ) : mc (M + 3) .zx [ℓ] (fun _ => none) = D.N15.zxAt (M + 3) ℓ := by
  have h1 : ctrlWires (M + 3) [ℓ] (fun _ => none) = [] :=
    List.filter_eq_nil_iff.2 (fun j _ => by simp)
  have h2 : whiteWires (M + 3) [ℓ] (fun _ => none) = [] :=
    List.filter_eq_nil_iff.2 (fun j _ => by simp)
  unfold mc
  rw [h1, h2]
  simp [canonAt, colourW, drawn, D.N15.zxAt]

/-- **The decoded negation.** `D(ℰ⁰_{k,ℓ}(X))` is `X` on the wire `ℓ`. -/
theorem dec_encNeg (k ℓ : ℕ) (hk : k + ℓ + 1 = M + 3) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encNeg (M + 3) k ℓ 0))) (xAt (M + 3) ℓ) := by
  have hℓ : ℓ < M + 3 := by omega
  have e : encNeg (M + 3) k ℓ 0 = encL (M + 3) (.Z ℓ) ++
      ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) := by
    rw [show k = M + 3 - 1 - ℓ by omega]; rfl
  rw [e, decW_append]
  have hZ : Derivable (theory (M + 3)) (decW (M + 3) (wordOf (encL (M + 3) (.Z ℓ))))
      (place1 (M + 3) ℓ z) := by
    rcases ℓ with _ | ℓ
    · exact lemma86_Z_lo ih
    · exact lemma86_Z_hi ih ℓ (by omega)
  -- the mixed letters merge into the single-qubit `ZX`
  set ws := lowHigh ℓ 1 k with hws_def
  have hlen : ws.length = ℓ + k := lowHigh_length ℓ 1 k
  set sOf : ℕ → ℕ := fun i => i / 2 ^ ℓ * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + i % 2 ^ ℓ with hsOf
  have hmid : ∀ i q, (sOf i).testBit q =
      if q < ℓ then (i % 2 ^ ℓ).testBit q else if q < ℓ + 1 then (0 : ℕ).testBit (q - ℓ)
        else (i / 2 ^ ℓ).testBit (q - (ℓ + 1)) := fun i q =>
    testBit_mid _ _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos ℓ)) (by norm_num)
  have hbt : ∀ i, (sOf i).testBit ℓ = false := fun i => by
    rw [hmid, if_neg (by omega), if_pos (by omega)]; simp
  have hl : ((grid k ℓ).map fun p =>
        PG.zx (gx (M + 3) (p.1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + p.2))
          (gx (M + 3) (p.1 * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + p.2))) =
      (List.range (2 ^ ws.length)).map fun i =>
        PG.zx (gx (M + 3) (if true then sOf i ^^^ 2 ^ ℓ else sOf i)) (gx (M + 3) (sOf i))
          (gx (M + 3) (sOf i ^^^ 2 ^ ℓ)) := by
    simp only [grid_eq, List.map_map, if_true]
    rw [hlen, show (2 : ℕ) ^ (ℓ + k) = 2 ^ k * 2 ^ ℓ by rw [pow_add, mul_comm]]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    have e1 : i / 2 ^ ℓ * 2 ^ (ℓ + 1) + 0 * 2 ^ ℓ + i % 2 ^ ℓ = sOf i := rfl
    have e2 : i / 2 ^ ℓ * 2 ^ (ℓ + 1) + 1 * 2 ^ ℓ + i % 2 ^ ℓ = sOf i ^^^ 2 ^ ℓ := by
      rw [← add_two_pow_eq_xor (hbt i)]; simp only [hsOf]; ring
    rw [e1, e2]
  have hnone : ∀ w ∈ ws, (fun _ => (none : Option Bool)) w = none := fun _ _ => rfl
  have hd := decode_zx_list ih true (t := ℓ) hℓ ws (lowHigh_nodup ℓ 1 k)
    (by rw [hws_def, mem_lowHigh]; omega) (by intro w hw; rw [hws_def, mem_lowHigh] at hw; omega)
    (fun _ => none) rfl sOf (by
      intro i hi
      refine ⟨?_, hbt i, ?_⟩
      · have := state_lt i 0 ℓ 1 k (by rw [hlen] at hi; exact hi) (by norm_num)
        rw [← hk, show k + ℓ + 1 = ℓ + 1 + k by omega]; exact this
      · apply ctlOf_eq_bitsOn ws (lowHigh_nodup ℓ 1 k) _ ℓ (sOf i) i
          (by rw [hws_def, mem_lowHigh]; omega)
        · intro r hr
          rw [hlen] at hr
          exact testBit_state i 0 ℓ 1 k r hr (by norm_num)
        · intro j hj hjw
          rw [hws_def, mem_lowHigh] at hjw
          have : j = ℓ := by omega
          subst this
          simp [ctlOf])
  rw [idleOn_of_none ws _ hnone, Bool.not_true, show Kind.sgnZX false = .zx from rfl,
    mc_none_zx, ← hl] at hd
  refine (dmul hZ hd).trans ?_
  refine (dmul (place1_placeG z (M + 3) ℓ hℓ) (Derivable.refl _)).trans ?_
  unfold D.N15.zxAt xAt
  refine (D.N15.placeG_mul1 ℓ hℓ z (zx 0)).symm.trans ?_
  exact (D.N15.placeG_der1 ℓ hℓ (by omega) (one_x (ih 1 (by omega)))).trans
    (place1_placeG x (M + 3) ℓ hℓ).symm

end Swap2

end QCert.RealCliffordCH.Sec8.E
