/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (357): the `CZ` of the target and wire `1` turns `ZX` into `XZ`

The paper's proof, conjugated by the swaps of the wires `1, 2` ((353)) and
`0, 1`: then the `CZ` is the box on wire `0` controlled by the wires `1, 2`
((f3), `cz_box`), and the `ZX`, `XZ` have their target on wire `1`.  By (309)
over every colouring of the wires `3, …` (`mergeListB0`) the box is a product
of boxes with every control; those with a white control pass the `ZX` ((347))
and the other boxes ((335)) and cancel pairwise ((311)), leaving the box with
every control black, which conjugates the `ZX` into the `XZ` by (333), (334)
and (299).
-/
import QCert.RealCliffordCH.Sec8.D.N15.E355c

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-! ## Gates at the bottom -/

theorem atBot_atBot {k m : ℕ} (g : Circ k) (hkm : k ≤ m) :
    ∀ N, m ≤ N → atBot N (atBot m g) = atBot N g := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [atBot_self]
  | succ M hM ihM =>
    rw [atBot_succ M _ (by omega), atBot_succ M _ (by omega), ihM]

/-- The `CZ` of the wires `0, 2` (the `CZ` of the wires `0, 1` conjugated by the
swap of the wires `1, 2`) is the box on wire `1` controlled by the wires `0, 2`
conjugated by the swap of the wires `0, 1`: (f3), on three wires. -/
theorem cz_box3 :
    Derivable (theory 3) (swAt 3 0 * box 2 * swAt 3 0) (swAt 3 1 * czAt 3 0 1 * swAt 3 1) := by
  have hf3 := N8.rule_full Rule.f3
  have e1 : (swap : Circ 3) = swAt 3 0 := rfl
  have e2 : (shift swap : Circ 3) = swAt 3 1 := by simp [swAt, place2, pad_zero2]
  have e3 : (shift cz : Circ 3) = box 2 := rfl
  have e4 : (cz : Circ 3) = czAt 3 0 1 := by
    rw [czAt, placeG_pair 3 cz (by norm_num)]; rfl
  rw [drawn_three', drawn_three', e1, e2, e3, e4] at hf3
  have s0 := swsw 3 0 (by omega)
  have s1 := swsw 3 1 (by omega)
  set S0 := swAt 3 0
  set S1 := swAt 3 1
  set C := czAt 3 0 1
  -- `S0 B S0 = S1 (S1 S0 B) S0 = S1 (C S1 S0) S0 = S1 C S1`
  have k1 : Derivable (theory 3) (S0 * box 2 * S0) (S1 * (S1 * S0 * box 2) * S0) := by
    have := dright (S0 * box 2 * S0) s1
    rw [one_mul] at this
    refine this.symm.trans (der_of_eq ?_)
    simp only [mul_assoc]
  have k2 : Derivable (theory 3) (S1 * (S1 * S0 * box 2) * S0) (S1 * (C * S1 * S0) * S0) :=
    dright _ (dleft _ hf3)
  have k3 : Derivable (theory 3) (S1 * (C * S1 * S0) * S0) (S1 * C * S1) := by
    have e : S1 * (C * S1 * S0) * S0 = S1 * C * S1 * (S0 * S0) := by simp only [mul_assoc]
    rw [e]
    have := dleft (S1 * C * S1) s0
    rwa [mul_one] at this
  exact k1.trans (k2.trans k3)

theorem cz_box {N : ℕ} (hN : 3 ≤ N) :
    Derivable (theory N)
      (swAt N 0 * mc N .box [0] (ctlOr (ctlAt 1 true) (ctlAt 2 true)) * swAt N 0)
      (swAt N 1 * czAt N 0 1 * swAt N 1) := by
  have h := der_atBot cz_box3 N hN
  rw [atBot_mul, atBot_mul, atBot_mul, atBot_mul, atBot_swAt 0 (by omega) N hN,
    atBot_swAt 1 (by omega) N hN] at h
  have eB : atBot N (box 2) = mc N .box [0] (ctlOr (ctlAt 1 true) (ctlAt 2 true)) := by
    rw [N13.mc_atBot (k := 3) .box [0] _ rfl (by simp) (by simp)
      (fun j hj => by simp [ctlOr, ctlAt]; omega) N hN]
    congr 1
  have eC : atBot N (czAt 3 0 1) = czAt N 0 1 := by
    rw [czAt, czAt, placeG_pair 3 cz (by norm_num), placeG_pair N cz (by omega),
      atBot_atBot cz (by norm_num) N hN]
  rwa [eB, eC] at h

/-! ## Boxes over every colouring -/

/-- The boxes on wire `0` over every colouring of the wires `ws`, the other
controls fixed, merge into the box with the wires `ws` idle. -/
theorem mergeListB0 {M : ℕ} (ih : IH (M + 3)) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → 0 ∉ ws → (∀ w ∈ ws, w < M + 3) →
      base 0 = none →
      Derivable (theory (M + 3))
        (drawn ((List.range (2 ^ ws.length)).map fun i => mc (M + 3) .box [0] (bitsOn ws i base)))
        (mc (M + 3) .box [0] (idleOn ws base))
  | [], base, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil, drawn_one',
      bitsOn, idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, htw, hws, hb => by
    have hnd' := List.nodup_cons.1 hnd
    have hwt : w ≠ 0 := fun e => htw (by simp [e])
    have ih' := mergeListB0 ih ws (setCtl base w none) hnd'.2 (fun h => htw (by simp [h]))
      (fun x hx => hws x (by simp [hx])) (by simp [setCtl, Ne.symm hwt, hb])
    refine Derivable.trans ?_ ih'
    rw [List.length_cons, pow_succ, mul_comm, range_double, drawn_flatMap]
    apply drawn_map_congr
    intro i _
    have e0 : bitsOn (w :: ws) (2 * i) base = setCtl (bitsOn ws i base) w (some false) := by
      simp only [bitsOn]; congr 2 <;> simp [Nat.mul_div_cancel_left]
    have e1 : bitsOn (w :: ws) (2 * i + 1) base = setCtl (bitsOn ws i base) w (some true) := by
      simp only [bitsOn]; congr 2 <;> simp [Nat.mul_add_div] <;> omega
    rw [e0, e1, ← setCtl_bitsOn ws i base w none hnd'.1]
    have hct : bitsOn ws i base 0 = none := by
      rw [bitsOn_of_not_mem ws i base 0 (fun h => htw (by simp [h]))]; exact hb
    exact mergeC M ih (bitsOn ws i base) hct w (by omega) (hws w (by simp)) false

end QCert.RealCliffordCH.Sec8.D.N15
