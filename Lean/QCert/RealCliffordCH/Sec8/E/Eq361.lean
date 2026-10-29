/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (361): the decoding of `X_[0,3]X_[1,2]`

`D(X_[0,3]X_[1,2]) = D((-1)_[0]X_[0,3]) D((-1)_[3]X_[1,2])`, and with the
recursion of Definition 8.3 this is, in drawn order,

    R, B₁, B₀, X₀ʷ, X₀ᵇ, R, Z₀ᵇ, Z₀ʷ

with `R` the `XZ` on wire `1` (black on `0`), `B₁` the box on wire `1` (black
on `0`), `B₀` the box on wire `0` (black on `1`), `X₀ʷ`, `X₀ᵇ` the `XZ` on wire
`0` (white, resp. black, on `1`), `Z₀ᵇ`, `Z₀ʷ` the `ZX` there; every other
control is white.  The paper's chain: Lemma 8.5 for the last five letters,
then (355), (317), (81), (311), (81), (354).  Here Lemma 8.5 is the paper's
own argument for that instance: by (354) over every colouring of the wires
`1, …` (`mergeListZ`) the single-qubit `XZ` on wire `0` is
`x = P · X₀ᵇ · X₀ʷ`, every factor of `P` commutes with `R` by (352), so
`Z₀ʷ Z₀ᵇ · R · X₀ᵇ X₀ʷ = z R x` (`z` the single-qubit `ZX`), which is the
`XZ` on wire `1` white on `0` by (359) under the swap of the wires `0, 1`.
The rest: `R R = B₁` (355), `B₀ R B₀ = R⁻¹` (`box_inv_rot`), (311), (317),
(354) (`alg361`).

Every step was checked numerically at `N = 3, 4, 5` (`gen/sec8/e/m361.py`).
The statement belongs to `D/N15.lean`'s list, but its proof uses the
Appendix E toolkit, which imports that file; it is stated here as
`D.eq361`.
-/
import QCert.RealCliffordCH.Sec8.E.Rule31

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Tools -/

theorem isOnes_1_1 : IsOnes 1 1 :=
  ⟨fun j hj => by interval_cases j; decide, by decide⟩

theorem bitOf_small {s j : ℕ} (h : s < 2 ^ j) : bitOf s j = 0 := by
  simp [bitOf, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

theorem bitsOn_zero_apply : ∀ (ws : List ℕ) (base : ℕ → Option Bool) (j : ℕ),
    bitsOn ws 0 base j = if j ∈ ws then some false else base j
  | [], base, j => by simp [bitsOn]
  | w :: ws, base, j => by
    simp only [bitsOn, Nat.zero_div, Nat.zero_mod, setCtl, bitsOn_zero_apply ws, List.mem_cons]
    by_cases h1 : j = w <;> by_cases h2 : j ∈ ws <;> simp [h1, h2]

/-- Above the first index some wire of `ws` is black. -/
theorem bitsOn_black : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool), ws.Nodup →
    0 < i → i < 2 ^ ws.length → ∃ j ∈ ws, bitsOn ws i base j = some true
  | [], i, _, _, h0, h => by simp at h; omega
  | w :: ws, i, base, hnd, h0, h => by
    have hnd' := List.nodup_cons.1 hnd
    by_cases hi : i % 2 = 1
    · exact ⟨w, by simp, by simp [bitsOn, setCtl, hi]⟩
    · obtain ⟨j, hj, hb⟩ := bitsOn_black ws (i / 2) base hnd'.2 (by omega) (by
        rw [List.length_cons, pow_succ] at h; omega)
      refine ⟨j, by simp [hj], ?_⟩
      have hjw : j ≠ w := fun e => hnd'.1 (e ▸ hj)
      simp only [bitsOn, setCtl, if_neg hjw]; exact hb

/-- (354) for the `(-1)ᵃ ZX` on wire `t`, any controls. -/
theorem mergeAtZ {M : ℕ} (ih : IH (M + 3)) (a : Bool) {t : ℕ} (ht : t < M + 3)
    (c : ℕ → Option Bool) (hc : c t = none) {w : ℕ} (hwt : w ≠ t) (hw : w < M + 3) (b : Bool) :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w (some b)),
        mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w (some !b))])
      (mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w none)) := by
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have hπ0 : frm [t] 0 = t := frm_getD hnd hps (by simp)
  set w' := pos (netOf [t]) w
  have hw' : w' < M + 3 := pos_lt _ (netOf_ok hnd hps) w hw
  have hw'0 : w' ≠ 0 := by
    intro h; apply hwt; rw [← frm_pos [t] w, show pos (netOf [t]) w = 0 from h, hπ0]
  have hsw := mcSwapAll ih
  have fr : ∀ v, Derivable (theory (M + 3))
      (placedBy (M + 3) (netOf [t]) (mc (M + 3) (Kind.sgnZX a) [0] (setCtl (c ∘ frm [t]) w' v)))
      (mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w v)) := by
    intro v
    have := frame hsw hnd hps (Kind.sgnZX a) [0] (setCtl c w v) (by simp [D.N15.kindSp_sgnZX])
      (by simp) (by simp)
    rw [setCtl_frm] at this
    simpa [hπ0] using this
  have hc' : (c ∘ frm [t]) 0 = none := by simp [hπ0, hc]
  have := via_frame (L := [mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w (some b)),
      mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w (some !b))])
    (R := [mc (M + 3) (Kind.sgnZX a) [t] (setCtl c w none)])
    hnd hps (List.Forall₂.cons (fr _) (List.Forall₂.cons (fr _) List.Forall₂.nil))
    (List.Forall₂.cons (fr _) List.Forall₂.nil) (by
      rw [drawn_single]; exact D.N15.mergeCZ M ih a _ hc' w' (by omega) hw' b)
  rwa [drawn_single] at this

/-- The algebra of the chain. -/
theorem alg361 {Q : Type*} [Monoid Q] {R Ri B1 B0 X0w X0b Z0w Z0b R2 Xi x z Px : Q}
    (hR2 : R * R = B1) (hB1 : B1 * B1 = 1) (hRi : Ri * R = 1) (hB0R : B0 * R * B0 = Ri)
    (hB0 : B0 * B0 = 1) (hXZb : X0b * Z0b = 1) (hXZw : X0w * Z0w = 1)
    (hx : x = Px * (X0b * X0w)) (hPx : Px * R = R * Px) (hzx : z * x = 1)
    (h359 : z * R * x = R2) (hm : R2 * R = Xi) :
    Z0w * (Z0b * R * X0b) * X0w * (B0 * B1 * R) = Xi * B0 := by
  have hYW : X0b * X0w * (Z0w * Z0b) = 1 := by
    calc X0b * X0w * (Z0w * Z0b) = X0b * (X0w * Z0w) * Z0b := by simp only [mul_assoc]
      _ = 1 := by rw [hXZw, mul_one, hXZb]
  have hzP : z * Px = Z0w * Z0b := by
    calc z * Px = z * Px * (X0b * X0w * (Z0w * Z0b)) := by rw [hYW, mul_one]
      _ = z * (Px * (X0b * X0w)) * (Z0w * Z0b) := by simp only [mul_assoc]
      _ = Z0w * Z0b := by rw [← hx, hzx, one_mul]
  have hWRY : Z0w * Z0b * R * (X0b * X0w) = R2 := by
    calc Z0w * Z0b * R * (X0b * X0w) = z * Px * R * (X0b * X0w) := by rw [hzP]
      _ = z * (Px * R) * (X0b * X0w) := by simp only [mul_assoc]
      _ = z * R * (Px * (X0b * X0w)) := by rw [hPx]; simp only [mul_assoc]
      _ = R2 := by rw [← hx, h359]
  have hR3 : R * R * R = Ri := by
    calc R * R * R = (Ri * R) * (R * R * R) := by rw [hRi, one_mul]
      _ = Ri * ((R * R) * (R * R)) := by simp only [mul_assoc]
      _ = Ri := by rw [hR2, hB1, mul_one]
  have hB0Ri : B0 * Ri = R * B0 := by
    calc B0 * Ri = (B0 * B0) * R * B0 := by rw [← hB0R]; simp only [mul_assoc]
      _ = R * B0 := by rw [hB0, one_mul]
  calc Z0w * (Z0b * R * X0b) * X0w * (B0 * B1 * R)
      = (Z0w * Z0b * R * (X0b * X0w)) * (B0 * (R * R * R)) := by
        rw [← hR2]; simp only [mul_assoc]
    _ = R2 * (R * B0) := by rw [hWRY, hR3, hB0Ri]
    _ = Xi * B0 := by rw [← mul_assoc, hm]

/-! ## The letters -/

section Letters

variable (M : ℕ)

abbrev R61 : Circ (M + 3) := mc (M + 3) .xz [1] (ctlOf 1 1)
abbrev Ri61 : Circ (M + 3) := mc (M + 3) .zx [1] (ctlOf 1 1)
abbrev B161 : Circ (M + 3) := mc (M + 3) .box [1] (ctlOf 1 1)
abbrev B061 : Circ (M + 3) := mc (M + 3) .box [0] (ctlOf 3 0)
abbrev X0w61 : Circ (M + 3) := mc (M + 3) .xz [0] (ctlOf 0 0)
abbrev X0b61 : Circ (M + 3) := mc (M + 3) .xz [0] (ctlOf 3 0)
abbrev Z0w61 : Circ (M + 3) := mc (M + 3) .zx [0] (ctlOf 0 0)
abbrev Z0b61 : Circ (M + 3) := mc (M + 3) .zx [0] (ctlOf 3 0)
abbrev R261 : Circ (M + 3) := mc (M + 3) .xz [1] (ctlOf 0 1)
abbrev Xi61 : Circ (M + 3) := mc (M + 3) .xz [1] (colOn 2 (M + 3) fun _ => false)

variable {M}

theorem two_pow_ge8 : 8 ≤ 2 ^ (M + 3) := by
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (M + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_pow_ge8' : 8 ≤ 2 ^ (M + 2 + 1) := two_pow_ge8

theorem dl10 : dZX1 (M + 3) 1 0 = R61 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZX1_mc (M + 2)]
  have ht : tOf (M + 2 + 1) 1 = 1 := tOf_eq isOnes_1_1 (by omega)
  have hk : kindZX (M + 2 + 1) 1 0 = .xz := by
    unfold kindZX; rw [ht]; have hb : bitOf (gray 1) 1 = 0 := by decide
    simp [hb]
  rw [hk, ht, show gray 1 = 1 by decide]

theorem dl00 : dZX1 (M + 3) 0 0 = X0w61 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZX1_mc (M + 2)]
  have ht : tOf (M + 2 + 1) 0 = 0 := tOf_eq isOnes_zero (by omega)
  have hk : kindZX (M + 2 + 1) 0 0 = .xz := by
    unfold kindZX; rw [ht]; have hb : bitOf (gray 0) 0 = 0 := by decide
    simp [hb]
  rw [hk, ht, show gray 0 = 0 by decide]

theorem dl01 : dZX1 (M + 3) 0 1 = Z0w61 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZX1_mc (M + 2)]
  have ht : tOf (M + 2 + 1) 0 = 0 := tOf_eq isOnes_zero (by omega)
  have hk : kindZX (M + 2 + 1) 0 1 = .zx := by
    unfold kindZX; rw [ht]; have hb : bitOf (gray 0) 0 = 0 := by decide
    simp [hb]
  rw [hk, ht, show gray 0 = 0 by decide]

theorem dl21 : dZX1 (M + 3) 2 1 = X0b61 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZX1_mc (M + 2)]
  have ht : tOf (M + 2 + 1) 2 = 0 := tOf_eq isOnes_2_0 (by omega)
  have hk : kindZX (M + 2 + 1) 2 1 = .xz := by
    unfold kindZX; rw [ht]; have hb : bitOf (gray 2) 0 = 1 := by decide
    simp [hb]
  rw [hk, ht, show gray 2 = 3 by decide]

theorem dl20 : dZX1 (M + 3) 2 0 = Z0b61 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZX1_mc (M + 2)]
  have ht : tOf (M + 2 + 1) 2 = 0 := tOf_eq isOnes_2_0 (by omega)
  have hk : kindZX (M + 2 + 1) 2 0 = .zx := by
    unfold kindZX; rw [ht]; have hb : bitOf (gray 2) 0 = 1 := by decide
    simp [hb]
  rw [hk, ht, show gray 2 = 3 by decide]

theorem dz1 : dZZ1 (M + 3) 1 = B161 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZZ1_mc (M + 2), tOf_eq isOnes_1_1 (by omega), show gray 1 = 1 by decide]

theorem dz2 : dZZ1 (M + 3) 2 = B061 M := by
  have h8 := two_pow_ge8' (M := M)
  rw [dZZ1_mc (M + 2), tOf_eq isOnes_2_0 (by omega), show gray 2 = 3 by decide]

/-- The decoding of `X_[0,3]X_[1,2]`, letter by letter. -/
theorem dec361 : dec (M + 3) (Xx (M + 3) 0 3 1 2) =
    drawn [drawn [R61 M, drawn [B161 M, B061 M]],
      drawn [X0w61 M, drawn [X0b61 M, R61 M, Z0b61 M], Z0w61 M]] := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_Xx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  rw [show dZX (M + 3) 3 1 2 = drawn [dZX1 (M + 3) 1 0, drawn [dZZ1 (M + 3) 1, dZZ1 (M + 3) 2]]
      from rfl,
    show dZX (M + 3) 0 0 3 = drawn [dZX1 (M + 3) 0 0,
      drawn [dZX1 (M + 3) 2 1, dZX1 (M + 3) 1 0, dZX1 (M + 3) 2 0], dZX1 (M + 3) 0 1] from rfl]
  rw [dl10, dl00, dl01, dl21, dl20, dz1, dz2]

end Letters

/-! ## The pieces -/

section Pieces

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- The wires `1, …, M + 2`. -/
abbrev W61 (M : ℕ) : List ℕ := 1 :: D.N15.S8 M

omit ih in
theorem W61_nodup : (W61 M).Nodup := by
  refine List.nodup_cons.2 ⟨?_, D.N15.S8_nodup⟩
  rw [D.N15.mem_S8]; omega

omit ih in
theorem mem_W61 {j : ℕ} : j ∈ W61 M ↔ 1 ≤ j ∧ j < M + 3 := by
  simp only [W61, List.mem_cons, D.N15.mem_S8]; omega

/-- The colourings of the wires `1, …` of the `XZ` on wire `0`. -/
abbrev f61 (M i : ℕ) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX true) [0] (bitsOn (W61 M) i fun _ => none)

omit ih in
theorem f61_zero : f61 M 0 = X0w61 M := Net.mc_congr _ _ _ (fun j hj => by
  rw [bitsOn_zero_apply]
  by_cases hjw : j ∈ W61 M
  · rw [if_pos hjw]
    have := mem_W61.1 hjw
    simp [ctlOf, show j ≠ 0 by omega, bitOf_small (show 0 < 2 ^ j by positivity)]
  · rw [if_neg hjw]
    have : j = 0 := by rw [mem_W61] at hjw; omega
    simp [ctlOf, this])

omit ih in
theorem f61_one : f61 M 1 = X0b61 M := Net.mc_congr _ _ _ (fun j hj => by
  rw [show bitsOn (W61 M) 1 (fun _ => none) =
    setCtl (bitsOn (D.N15.S8 M) 0 (fun _ => none)) 1 (some true) from rfl]
  simp only [setCtl]
  by_cases h1 : j = 1
  · subst h1; simp [ctlOf, bitOf]
  · rw [if_neg h1, bitsOn_zero_apply]
    by_cases hjS : j ∈ D.N15.S8 M
    · rw [if_pos hjS]
      have := D.N15.mem_S8.1 hjS
      simp [ctlOf, show j ≠ 0 by omega, bitOf_small (show 3 < 2 ^ j by
        calc 3 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this.1)]
    · rw [if_neg hjS]
      have : j = 0 := by rw [D.N15.mem_S8] at hjS; omega
      simp [ctlOf, this])

omit ih in
/-- `R` written for (352). -/
theorem R61_eq : R61 M = mc (M + 3) (Kind.sgnZX true) [1]
    (ctlOr (ctlAt 0 true) (colOn 2 (M + 3) fun _ => false)) := Net.mc_congr _ _ _ (fun j hj => by
  rcases j with _ | _ | j
  · simp [ctlOf, ctlOr, ctlAt, colOn, bitOf]
  · simp [ctlOf, ctlOr, ctlAt, colOn]
  · simp [ctlOf, ctlOr, ctlAt, colOn, hj,
      bitOf_small (show 1 < 2 ^ (j + 2) by
        calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))])

/-- Every colouring but the first two commutes with `R` ((352)). -/
theorem f61_comm {i : ℕ} (h2 : 2 ≤ i) (hi : i < 2 ^ (M + 2)) : D.Comm (M + 3) (f61 M i) (R61 M) := by
  set x : ℕ → Bool := fun j => (bitsOn (W61 M) i (fun _ => none) j).getD false
  obtain ⟨j, hj, hb⟩ := bitsOn_black (D.N15.S8 M) (i / 2) (fun _ => none) D.N15.S8_nodup
    (by omega) (by simp only [D.N15.S8, List.length_map, List.length_range]; rw [pow_succ] at hi; omega)
  have hj' := D.N15.mem_S8.1 hj
  have hj1 : j ≠ 1 := by omega
  have hxj : x j = true := by
    simp only [x, W61, bitsOn, setCtl, if_neg hj1, hb, Option.getD_some]
  have hd : DiffOn 2 (M + 3) x (fun _ => false) := ⟨j, hj'.1, hj'.2, by simp [hxj]⟩
  have h := D.eq352 (M + 3) (by omega) ih x (fun _ => false) hd true true (decide (i % 2 = 1)) true
  have e1 : mc (M + 3) (Kind.sgnZX true) [0]
      (ctlOr (ctlAt 1 (decide (i % 2 = 1))) (colOn 2 (M + 3) x)) = f61 M i :=
    Net.mc_congr _ _ _ (fun k hk => by
      rcases k with _ | _ | k
      · rw [bitsOn_of_not_mem _ _ _ 0 (by rw [mem_W61]; omega)]; simp [ctlOr, ctlAt, colOn]
      · simp [ctlOr, ctlAt, colOn, W61, bitsOn, setCtl]
      · obtain ⟨b, hb'⟩ := D.N15.bitsOn_mem (W61 M) i (fun _ => none) (k + 2)
          (by rw [mem_W61]; omega)
        simp [ctlOr, ctlAt, colOn, hk, x, hb'])
  rw [e1, ← R61_eq] at h
  exact h

/-- The single-qubit `XZ` on wire `0` is `P · X₀ᵇ · X₀ʷ` ((354) over every colouring). -/
theorem x61 : Derivable (theory (M + 3)) (D.N15.xzAt (M + 3) 0)
    (drawn ((List.range (2 ^ (M + 2) - 2)).map fun i => f61 M (2 + i)) * (X0b61 M * X0w61 M)) := by
  have hm := D.N15.mergeListZ ih true (W61 M) (fun _ => none) W61_nodup
    (by rw [mem_W61]; omega) (fun w hw => (mem_W61.1 hw).2) rfl
  have eI : mc (M + 3) (Kind.sgnZX true) [0] (idleOn (W61 M) fun _ => none) =
      D.N15.xzAt (M + 3) 0 := by
    rw [Net.mc_congr _ _ _ (c' := fun _ => none) (fun j hj => by
      rw [D.N15.idleOn_apply]; split_ifs <;> rfl)]
    simp [mc, ctrlWires, whiteWires, canonAt, colourW, drawn, D.N15.xzAt, Kind.sgnZX]
  rw [eI] at hm
  have hL : 2 ^ (W61 M).length = 2 + (2 ^ (M + 2) - 2) := by
    simp only [W61, List.length_cons, D.N15.S8, List.length_map, List.length_range]
    have : 4 ≤ 2 ^ (M + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (M + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show M + 1 + 1 = M + 2 by omega]; omega
  rw [hL, List.range_add, List.map_append, SE.drawn_append] at hm
  have e2 : (List.range 2).map (fun i => f61 M i) = [f61 M 0, f61 M 1] := rfl
  rw [List.map_map, e2, Net.drawn_cons, Net.drawn_cons, f61_zero, f61_one] at hm
  refine hm.symm.trans (der_of_eq ?_)
  simp only [drawn, List.reverse_nil, List.prod_nil, one_mul]
  rfl

/-- `P` commutes with `R`. -/
theorem P61_comm : Derivable (theory (M + 3))
    (drawn ((List.range (2 ^ (M + 2) - 2)).map fun i => f61 M (2 + i)) * R61 M)
    (R61 M * drawn ((List.range (2 ^ (M + 2) - 2)).map fun i => f61 M (2 + i))) := by
  have h := D.N13.comm_drawn_left (c := R61 M) ((List.range (2 ^ (M + 2) - 2)).map fun i => f61 M (2 + i))
    (fun g hg => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      have := List.mem_range.1 hi
      exact f61_comm ih (by omega) (by omega))
  unfold D.Comm at h
  rw [drawn_two, drawn_two] at h
  exact h.symm

/-- The single-qubit `ZX` and `XZ` on wire `0` are inverse. -/
theorem zx61 : Derivable (theory (M + 3)) (D.N15.zxAt (M + 3) 0 * D.N15.xzAt (M + 3) 0) 1 := by
  have d1 : Derivable (theory 1) ((zx 0 : Circ 1) * xz 0) 1 :=
    ih 1 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  exact (D.N15.placeG_mul1 0 (by omega) (zx 0) (xz 0)).symm.trans
    ((D.N15.placeG_der1 0 (by omega) (by omega) d1).trans (D.N15.placeG_one1 0 (by omega)))

/-- (359) under the swap of the wires `0, 1`: `z R x` is `R` white on `0`. -/
theorem h359_61 : Derivable (theory (M + 3))
    (D.N15.zxAt (M + 3) 0 * R61 M * D.N15.xzAt (M + 3) 0) (R261 M) := by
  have hS := swsw (M + 3) 0 (by omega)
  have h := (D.N15.eq359 (M + 3) (by omega) ih true (fun _ => false) 1 le_rfl (by omega) true).1
  have hsw := D.N15.mcSwapAll' ih
  have pl : ∀ g : Circ 1, Derivable (theory (M + 3))
      (swAt (M + 3) 0 * placeG (M + 3) g [1] * swAt (M + 3) 0) (placeG (M + 3) g [0]) := by
    intro g
    have := placeG_swap (N := M + 3) g (ps := [1]) (by simp) (by simp) rfl 0 (by omega)
    rw [D.N15.conj3] at this
    simpa [Net.tau] using this
  have fm : ∀ (v : Bool) (d : ℕ → Option Bool),
      (∀ j < M + 3, d j = setCtl (colOn 1 (M + 3) fun _ => false) 1 (some v) (Net.tau 0 j)) →
      Derivable (theory (M + 3))
        (swAt (M + 3) 0 * mc (M + 3) (Kind.sgnZX true) [0]
          (setCtl (colOn 1 (M + 3) fun _ => false) 1 (some v)) * swAt (M + 3) 0)
        (mc (M + 3) .xz [1] d) := by
    intro v d hd
    have := hsw 0 (by omega) (Kind.sgnZX true) [0]
      (setCtl (colOn 1 (M + 3) fun _ => false) 1 (some v)) rfl (by simp) (by simp)
    rw [D.N15.conj3] at this
    refine this.trans (der_of_eq ?_)
    rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
    exact Net.mc_congr _ _ _ (fun j hj => (hd j hj).symm)
  have fR := fm true (ctlOf 1 1) (fun j hj => by
    rcases j with _ | _ | j
    · simp [ctlOf, setCtl, colOn, Net.tau, bitOf]
    · simp [ctlOf, setCtl, colOn, Net.tau]
    · simp [ctlOf, setCtl, colOn, Net.tau, hj,
        bitOf_small (show 1 < 2 ^ (j + 2) by
          calc 1 < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))])
  have fR2 := fm false (ctlOf 0 1) (fun j hj => by
    rcases j with _ | _ | j
    · simp [ctlOf, setCtl, colOn, Net.tau, bitOf]
    · simp [ctlOf, setCtl, colOn, Net.tau]
    · simp [ctlOf, setCtl, colOn, Net.tau, hj, bitOf_small (show 0 < 2 ^ (j + 2) by positivity)])
  have k := D.N15.via_conj hS (L := [D.N15.xzAt (M + 3) 0, R61 M, D.N15.zxAt (M + 3) 0])
    (R := [R261 M])
    (List.Forall₂.cons (pl _) (List.Forall₂.cons fR (List.Forall₂.cons (pl _) List.Forall₂.nil)))
    (List.Forall₂.cons fR2 List.Forall₂.nil) (by rw [D.N15.drawn_one']; exact h)
  rwa [D.N15.drawn_three', D.N15.drawn_one'] at k

/-- (354): `R` then `R₂` is the `XZ` on wire `1` with wire `0` idle. -/
theorem merge61 : Derivable (theory (M + 3)) (R261 M * R61 M) (Xi61 M) := by
  have h := mergeAtZ ih true (t := 1) (by omega) (colOn 2 (M + 3) fun _ => false)
    (by simp [colOn]) (w := 0) (by omega) (by omega) true
  rw [drawn_two] at h
  have e1 : mc (M + 3) (Kind.sgnZX true) [1]
      (setCtl (colOn 2 (M + 3) fun _ => false) 0 (some true)) = R61 M :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | j
      · simp [ctlOf, setCtl, colOn, bitOf]
      · simp [ctlOf, setCtl, colOn]
      · simp [ctlOf, setCtl, colOn, hj,
          bitOf_small (show 1 < 2 ^ (j + 2) by
            calc 1 < 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))])
  have e2 : mc (M + 3) (Kind.sgnZX true) [1]
      (setCtl (colOn 2 (M + 3) fun _ => false) 0 (some !true)) = R261 M :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | j
      · simp [ctlOf, setCtl, colOn, bitOf]
      · simp [ctlOf, setCtl, colOn]
      · simp [ctlOf, setCtl, colOn, hj, bitOf_small (show 0 < 2 ^ (j + 2) by positivity)])
  have e3 : mc (M + 3) (Kind.sgnZX true) [1] (setCtl (colOn 2 (M + 3) fun _ => false) 0 none) =
      Xi61 M := Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | j
      · simp [setCtl, colOn]
      · simp [setCtl, colOn])
  rwa [e1, e2, e3] at h

end Pieces

end QCert.RealCliffordCH.Sec8.E

namespace QCert.RealCliffordCH.Sec8.D

open Circuit Net E

/-- (361): the decoding of `X_[0,3]X_[1,2]` is the box on wire `0` controlled by
wire `1` (black) and the wires above (white), followed by the `XZ` on wire
`1` controlled by the wires above (white). -/
theorem eq361 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (decW N (wordOf [Xx N 0 3 1 2]))
      (drawn [mc N .box [0] (ctlOr (ctlAt 1 true) (colOn 2 N fun _ => false)),
        mc N .xz [1] (colOn 2 N fun _ => false)]) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one, dec361]
  have eB : mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) fun _ => false)) = B061 M :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | j
      · simp [ctlOf, ctlOr, ctlAt, colOn]
      · simp [ctlOf, ctlOr, ctlAt, colOn, bitOf]
      · simp [ctlOf, ctlOr, ctlAt, colOn, hj,
          bitOf_small (show 3 < 2 ^ (j + 2) by
            calc 3 < 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))])
  rw [eB]
  have hR2 := rot_sq ih true (t := 1) (s := 1) (by omega)
  have hB1 := box_inv ih (t := 1) (s := 1) (by omega)
  have hRi := rot_inv ih true (t := 1) (s := 1) (by omega)
  have hB0R := box_inv_rot ih true (t := 1) (w := 0) (s := 1) (s' := 3) (by omega) (by omega)
    (by omega) (fun j h1 h0 => by
      rw [bitOf_small (show 1 < 2 ^ j by
          calc 1 < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)),
        bitOf_small (show 3 < 2 ^ j by
          calc 3 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega))])
  have hB0 := box_inv ih (t := 0) (s := 3) (by omega)
  have hXZb := rot_inv ih false (t := 0) (s := 3) (by omega)
  have hXZw := rot_inv ih false (t := 0) (s := 0) (by omega)
  rw [drawn_two] at hB1 hB0
  have key := alg361 (Q := (conGen (theory (M + 3))).Quotient)
    (R := (R61 M : (conGen (theory (M + 3))).Quotient)) (Ri := Ri61 M) (B1 := B161 M)
    (B0 := B061 M) (X0w := X0w61 M) (X0b := X0b61 M) (Z0w := Z0w61 M) (Z0b := Z0b61 M)
    (R2 := R261 M) (Xi := Xi61 M) (x := D.N15.xzAt (M + 3) 0) (z := D.N15.zxAt (M + 3) 0)
    (Px := drawn ((List.range (2 ^ (M + 2) - 2)).map fun i => f61 M (2 + i)))
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 hR2)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hB1)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hRi)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hB0R)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hB0)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hXZb)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hXZw)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (x61 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (P61_comm ih))
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 (zx61 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (h359_61 ih))
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 (merge61 ih))
  apply (Con.eq _).1
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one, Con.coe_mul]
  simp only [Con.coe_mul] at key
  rw [← key]
  simp only [mul_assoc]

end QCert.RealCliffordCH.Sec8.D
