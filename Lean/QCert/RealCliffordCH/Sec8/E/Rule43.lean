/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (43)

`D(H_[0,1]H_[3,2]) = G` (the gadget: `H` on wire `0`, box wire `1`, white
above), `D(H_[3,2]H_[4,5]) = A` (`H` on wire `0`, box wire `2`, black on `1`,
white above) and `D(X_[0,3]X_[1,2]) = Y = Xi B0` by (361).  The rule is
`G A = Y A Y` (monoid order).  The paper's chain works in the frame of
`P = P ⊗ P` on the wires `0, 1`:

* `G = P Bg P` (Rule (44)'s `gadget_pp44`) and `A = P A'' P`, with `Bg` the box
  on wire `1` black on `0`, `A''` the multi-controlled `H` on wire `1` with box
  wire `2`, black on `0` (Definition 2.4 in two frames and the Klein
  four-group of the three `P ⊗ P` on the wires `0, 1, 2`, from (130));
* `Bg = R R` ((355)), `R A'' = A'' Ri` ((333), (334) under the swap of the
  wires `0, 1`), so `Bg A'' = R A'' Ri`;
* `R A'' Ri = Xi A'' Zi` ((317), (349), (354));
* `P Xi P = Zi` and `P Zi P = Xi` ((360)), so `G A = Zi A Xi`.

The end is not the paper's: `B0 Zi B0 = Xi` (`box_inv_rot`, (354)), so
`Y = Xi B0 = B0 Zi`, and `Y A Y = B0 (Zi A Xi) B0 = B0 G A B0 = G A`, `B0`
passing `G` and `A` by (338).

Every step was checked numerically at `N = 3, 4, 5` (`gen/sec8/e/m43.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule44

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## The Klein four-group of `P ⊗ P` on three wires -/

section Klein

open WE
open Eng (L)

def ppL43 : List L := [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0]

def tp43 (ps : List ℕ) : Tk := Tk.p 2 ppL43 ps

def T43 : WE.Tbl := [([tp43 [0, 1], tp43 [1, 2]], [tp43 [0, 2]])]

/-- `P₀₂ P₀₁ = P₂₁` (monoid order), on three wires. -/
theorem runK1 : check 2 T43 [tp43 [0, 1], tp43 [2, 0]] [tp43 [2, 1]]
    [.sem 1 1 [tp43 [0, 2]] 1, .rw 1 0 true, .sem 0 2 [] 2, .sem 0 1 [tp43 [2, 1]] 0] = true := by
  decide +kernel

/-- `P₀₁ P₂₀ = P₂₁` (monoid order), on three wires. -/
theorem runK2 : check 2 T43 [tp43 [2, 0], tp43 [0, 1]] [tp43 [2, 1]]
    [.sem 0 1 [tp43 [0, 2]] 1, .sem 2 0 [tp43 [1, 2], tp43 [1, 2]] 0, .rw 1 0 false,
     .sem 0 2 [] 1, .sem 0 1 [tp43 [2, 1]] 0] = true := by
  decide +kernel

theorem T43_ok (ih : IH 3) : AllD 3 T43 := AllD.cons (D.W3T.td130 ih) (AllD.nil 3)

theorem circW_ppL43 : Eng.circW 2 ppL43 = (pp : Circ 2) := rfl

/-- The two Klein relations on `N` wires. -/
theorem klein43 {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (ppAt (M + 3) 2 0 * ppAt (M + 3) 0 1) (ppAt (M + 3) 2 1) ∧
    Derivable (theory (M + 3)) (ppAt (M + 3) 0 1 * ppAt (M + 3) 2 0) (ppAt (M + 3) 2 1) := by
  have ih3 : IH 3 := ih.mono (by omega)
  have k1 := check_sound ih3 (T43_ok ih3) runK1
  have k2 := check_sound ih3 (T43_ok ih3) runK2
  have e : ∀ ps : List ℕ, ps.Nodup → (∀ p ∈ ps, p < 3) → ps.length = 2 →
      atBot (M + 3) ((tp43 ps).circ 3) = ppAt (M + 3) (ps.getD 0 0) (ps.getD 1 0) := by
    intro ps hnd hps hl
    show atBot (M + 3) (placeG 3 (Eng.circW 2 ppL43) ps) = _
    rw [circW_ppL43, atBot_placeG _ hnd hps hl (M + 3) (by omega)]
    match ps, hl with
    | [a, b], _ => rfl
  have lift : ∀ {a b : List Tk}, Derivable (theory 3) (wcT 3 a) (wcT 3 b) →
      Derivable (theory (M + 3)) (atBot (M + 3) (wcT 3 a)) (atBot (M + 3) (wcT 3 b)) :=
    fun h => der_atBot h (M + 3) (by omega)
  have d1 := lift k1
  have d2 := lift k2
  simp only [wcT, List.map_cons, List.map_nil, drawn_two, D.N15.drawn_one', atBot_mul] at d1 d2
  rw [e [0, 1] (by decide) (by simp) rfl, e [2, 0] (by decide) (by simp) rfl,
    e [2, 1] (by decide) (by simp) rfl] at d1 d2
  exact ⟨d1, d2⟩

end Klein

/-! ## The gates -/

section Gates

variable (M : ℕ)

abbrev W2 : ℕ → Option Bool := colOn 2 (M + 3) fun _ => false
abbrev W3 : ℕ → Option Bool := colOn 3 (M + 3) fun _ => false
abbrev G43 : Circ (M + 3) := mc (M + 3) .hg [1, 0] (W2 M)
abbrev A43 : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (W3 M))
abbrev A2w : Circ (M + 3) := mc (M + 3) .hg [2, 1] (ctlOr (ctlAt 0 true) (W3 M))
abbrev Bg43 : Circ (M + 3) := mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (W2 M))
abbrev B043 : Circ (M + 3) := mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (W2 M))
abbrev R43 : Circ (M + 3) := mc (M + 3) .xz [1] (ctlOr (ctlAt 0 true) (W2 M))
abbrev Ri43 : Circ (M + 3) := mc (M + 3) .zx [1] (ctlOr (ctlAt 0 true) (W2 M))
abbrev Xw43 : Circ (M + 3) := mc (M + 3) .xz [1] (ctlOr (ctlAt 0 false) (W2 M))
abbrev Zw43 : Circ (M + 3) := mc (M + 3) .zx [1] (ctlOr (ctlAt 0 false) (W2 M))
abbrev Xi43 : Circ (M + 3) := mc (M + 3) .xz [1] (W2 M)
abbrev Zi43 : Circ (M + 3) := mc (M + 3) .zx [1] (W2 M)
abbrev P43 : Circ (M + 3) := ppAt (M + 3) 0 1

/-- The black versions. -/
abbrev Ab43 : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3)))
abbrev A2b : Circ (M + 3) := mc (M + 3) .hg [2, 1] (ctlOr (ctlAt 0 true) (blackOn 3 (M + 3)))
abbrev B2b : Circ (M + 3) :=
  mc (M + 3) .box [2] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))))

abbrev cR43 : ℕ → Option Bool := setCtl (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) 2 (some false)
abbrev cB43 : ℕ → Option Bool := setCtl (ctlOr (ctlAt 1 true) (blackOn 2 (M + 3))) 2 (some false)

end Gates

/-- Pointwise equality of two control assignments: unfold and split. -/
macro "ctl43" : tactic => `(tactic| (simp only [W2, W3, cR43, cB43, ctlOr, ctlAt, blackOn, colOn, setCtl,
  Function.comp, Net.tau, ctlOf, ctl2Of]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all))

/-! ## Colouring -/

section Colour

variable {N : ℕ}

/-- `X` on the wires `ws` on both sides turns black controls there white ((81)). -/
theorem colr43 (ws : List ℕ) (hnd : ws.Nodup) (K : Kind) (tg : List ℕ) (c c' : ℕ → Option Bool)
    (hc : ∀ j ∈ ws, j < N ∧ j ∉ tg ∧ c j = some true)
    (hc' : ∀ j < N, c' j = if j ∈ ws then some false else c j) :
    Derivable (theory N) (drawn (ws.map (xAt N)) * mc N K tg c * drawn (ws.map (xAt N)))
      (mc N K tg c') := by
  have h := D.N13.mc_colour N K tg c ws hnd hc
  rw [Net.colourW_eq] at h
  exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hc' j hj).symm)))

end Colour

section Rule43

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- `X` on the wires `3, …`. -/
abbrev U3 (M : ℕ) : Circ (M + 3) := drawn ((D.N15.S6 M).map (xAt (M + 3)))
/-- `X` on the wires `2, …`. -/
abbrev U2 (M : ℕ) : Circ (M + 3) := drawn ((D.N15.S8 M).map (xAt (M + 3)))

omit ih in
theorem U3_inv : Derivable (theory (M + 3)) (U3 M * U3 M) 1 :=
  D.xs_inv (M + 3) _ D.N15.S6_nodup (fun w hw => (D.N15.mem_S6.1 hw).2)

omit ih in
theorem U2_inv : Derivable (theory (M + 3)) (U2 M * U2 M) 1 :=
  D.xs_inv (M + 3) _ D.N15.S8_nodup (fun w hw => (D.N15.mem_S8.1 hw).2)

omit ih in
theorem U3_P : Derivable (theory (M + 3)) (U3 M * P43 M) (P43 M * U3 M) :=
  D.N8.pp_comm (by omega) (D.N8.highW_xs _ _ (fun j hj => by
    have := D.N15.mem_S6.1 hj; omega))

omit ih in
theorem U2_P : Derivable (theory (M + 3)) (U2 M * P43 M) (P43 M * U2 M) :=
  D.N8.pp_comm (by omega) (D.N8.highW_xs _ _ (fun j hj => (D.N15.mem_S8.1 hj).1))

omit ih in
/-- An equation `P a P = b` coloured by an involution `u` commuting with `P`. -/
theorem conjP_colour {u a b a' b' : Circ (M + 3)} (hu : Derivable (theory (M + 3)) (u * u) 1)
    (huP : Derivable (theory (M + 3)) (u * P43 M) (P43 M * u))
    (ha : Derivable (theory (M + 3)) (u * a * u) a') (hb : Derivable (theory (M + 3)) (u * b * u) b')
    (h : Derivable (theory (M + 3)) (P43 M * a * P43 M) b) :
    Derivable (theory (M + 3)) (P43 M * a' * P43 M) b' := by
  have hPu : Derivable (theory (M + 3)) (u * P43 M * u) (P43 M) :=
    D.N15.conj_of_comm hu (by unfold D.Comm; rw [drawn_two, drawn_two]; exact huP)
  have k := D.N15.via_conj hu (l := [P43 M, a, P43 M]) (L := [P43 M, a', P43 M]) (r := [b]) (R := [b'])
    (List.Forall₂.cons hPu (List.Forall₂.cons ha (List.Forall₂.cons hPu List.Forall₂.nil)))
    (List.Forall₂.cons hb List.Forall₂.nil)
    (by rw [D.N15.drawn_three', D.N15.drawn_one']; exact h)
  rwa [D.N15.drawn_three', D.N15.drawn_one'] at k

/-! ### `G = P Bg P` -/

theorem g_pp43 : Derivable (theory (M + 3)) (P43 M * G43 M * P43 M) (Bg43 M) := by
  have hP := pp_inv44 ih
  have h := gadget_pp44 ih
  -- `P G_b P = Bq_b`
  have hb : Derivable (theory (M + 3)) (P43 M * mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3)) * P43 M)
      (mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))) := by
    refine (dright _ (dleft _ h)).trans ?_
    have e : P43 M * (P43 M * mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) *
        P43 M) * P43 M = (P43 M * P43 M) * mc (M + 3) .box [1]
          (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) * (P43 M * P43 M) := by simp only [mul_assoc]
    rw [e]
    have := dmul (dmul hP (Derivable.refl (mc (M + 3) .box [1]
      (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))))) hP
    simpa using this
  refine conjP_colour U2_inv U2_P ?_ ?_ hb
  · exact colr43 _ D.N15.S8_nodup .hg [1, 0] _ _ (fun j hj => by
      have := D.N15.mem_S8.1 hj
      exact ⟨this.2, by simp; omega, by simp [blackOn]; omega⟩) (fun j hj => by
        by_cases hjw : j ∈ D.N15.S8 M
        · have := D.N15.mem_S8.1 hjw; rw [if_pos hjw]; simp [colOn]; omega
        · rw [if_neg hjw]; have : j < 2 := by by_contra h; exact hjw (D.N15.mem_S8.2 ⟨by omega, hj⟩)
          have h2 : ¬ 2 ≤ j := by omega
          simp [colOn, blackOn, h2])
  · exact colr43 _ D.N15.S8_nodup .box [1] _ _ (fun j hj => by
      have := D.N15.mem_S8.1 hj
      exact ⟨this.2, by simp; omega, by simp [ctlOr, ctlAt, blackOn]; omega⟩) (fun j hj => by
        by_cases hjw : j ∈ D.N15.S8 M
        · have := D.N15.mem_S8.1 hjw; rw [if_pos hjw]; simp [ctlOr, ctlAt, colOn]; omega
        · rw [if_neg hjw]; have : j < 2 := by by_contra h; exact hjw (D.N15.mem_S8.2 ⟨by omega, hj⟩)
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp [ctlOr, ctlAt, colOn, blackOn])


/-! ### Control assignments -/

omit ih in
theorem ctl_1_1 : ∀ j < M + 3, ctlOf 1 1 j = ctlOr (ctlAt 0 true) (W2 M) j := by
  intro j hj
  rcases j with _ | _ | j
  · simp [ctlOf, ctlOr, ctlAt, bitOf]
  · simp [ctlOf, ctlOr, ctlAt, colOn]
  · simp [ctlOf, ctlOr, ctlAt, colOn, hj, bitOf_small (show 1 < 2 ^ (j + 2) by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))]

omit ih in
theorem ctl_0_1 : ∀ j < M + 3, ctlOf 0 1 j = ctlOr (ctlAt 0 false) (W2 M) j := by
  intro j hj
  rcases j with _ | _ | j
  · simp [ctlOf, ctlOr, ctlAt, bitOf]
  · simp [ctlOf, ctlOr, ctlAt, colOn]
  · simp [ctlOf, ctlOr, ctlAt, colOn, hj, bitOf_small (show 0 < 2 ^ (j + 2) by positivity)]

omit ih in
theorem ctl_3_0 : ∀ j < M + 3, ctlOf 3 0 j = ctlOr (ctlAt 1 true) (W2 M) j := by
  intro j hj
  rcases j with _ | _ | j
  · simp [ctlOf, ctlOr, ctlAt, colOn]
  · simp [ctlOf, ctlOr, ctlAt, bitOf]
  · simp [ctlOf, ctlOr, ctlAt, colOn, hj, bitOf_small (show 3 < 2 ^ (j + 2) by
      calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega))]

omit ih in
theorem setW2 (b : Bool) : ∀ j < M + 3, setCtl (W2 M) 0 (some b) j = ctlOr (ctlAt 0 b) (W2 M) j := by
  intro j hj; rcases j with _ | j <;> simp [setCtl, ctlOr, ctlAt, colOn]

/-! ### `A = P A'' P` -/

/-- A frame of `hg_pp44` with the special wires `ps = [b, h]`: the box between
`P ⊗ P` on the wires `b, h`. -/
theorem hg_frame (b h : ℕ) (hb : b < 3) (hh : h < 3) (hbh : b ≠ h) (cH cB : ℕ → Option Bool)
    (hcH : ∀ j < M + 3, cH j = if j = b ∨ j = h then none else some true)
    (hcB : ∀ j < M + 3, cB j = if j = b then none else some true) :
    Derivable (theory (M + 3)) (mc (M + 3) .hg [b, h] cH)
      (ppAt (M + 3) b h * mc (M + 3) .box [b] cB * ppAt (M + 3) b h) := by
  have hnd : [b, h].Nodup := by simp [hbh]
  have hps : ∀ p ∈ [b, h], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [b, h] 0 = b := frm_getD hnd hps (by simp)
  have f1 : frm [b, h] 1 = h := frm_getD hnd hps (by simp)
  have hout : ∀ j, 2 ≤ j → j < M + 3 → frm [b, h] j ≠ b ∧ frm [b, h] j ≠ h ∧ frm [b, h] j < M + 3 := by
    intro j h2 hj
    obtain ⟨hm, hl⟩ := D.N15.frm_out' hnd hps (j := j) (by simpa using h2) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    exact ⟨hm.1, hm.2, hl⟩
  have fH := D.N15.frameAt' ih hnd hps .hg [0, 1] [b, h] cH (blackOn 2 (M + 3)) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0, f1])
    (fun j hj => by
      rcases j with _ | _ | j
      · rw [f0, hcH b (by omega)]; simp [blackOn]
      · rw [f1, hcH h (by omega)]; simp [blackOn]
      · obtain ⟨n0, n1, hl⟩ := hout (j + 2) (by omega) hj
        rw [hcH _ hl, if_neg (by omega)]; simp [blackOn]; omega)
  have fB := D.N15.frameAt' ih hnd hps .box [0] [b] cB (blackOn 1 (M + 3)) rfl (by simp)
    (by intro t ht; simp at ht; omega) (by simp [f0])
    (fun j hj => by
      rcases j with _ | _ | j
      · rw [f0, hcB b (by omega)]; simp [blackOn]
      · rw [f1, hcB h (by omega), if_neg (Ne.symm hbh)]; simp [blackOn]
      · obtain ⟨n0, n1, hl⟩ := hout (j + 2) (by omega) hj
        rw [hcB _ hl, if_neg n0]; simp [blackOn]; omega)
  have fP : Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [b, h]) (P43 M)) (ppAt (M + 3) b h) := by
    have hh := placeG_net (pp : Circ 2) (ps := [0, 1]) (by simp) (by intro p hp; simp at hp; omega)
      rfl (netOf [b, h]) (netOf_ok hnd hps)
    have e : ([0, 1] : List ℕ).map (pos (netOf [b, h]).reverse) = [b, h] := by
      simp only [List.map_cons, List.map_nil]
      exact congrArg₂ (· :: ·) f0 (congrArg (· :: []) f1)
    rw [e] at hh
    exact hh
  have k := via_frame hnd hps (l := [mc (M + 3) .hg [0, 1] (blackOn 2 (M + 3))])
    (r := [P43 M, D.Bx (M + 3), P43 M]) (L := [mc (M + 3) .hg [b, h] cH])
    (R := [ppAt (M + 3) b h, mc (M + 3) .box [b] cB, ppAt (M + 3) b h])
    (List.Forall₂.cons fH List.Forall₂.nil)
    (List.Forall₂.cons fP (List.Forall₂.cons fB (List.Forall₂.cons fP List.Forall₂.nil)))
    (by rw [D.N15.drawn_one', D.N15.drawn_three']; exact hg_pp44 ih)
  rwa [D.N15.drawn_one', D.N15.drawn_three'] at k

theorem a_pp43 : Derivable (theory (M + 3)) (P43 M * A43 M * P43 M) (A2w M) := by
  obtain ⟨k1, k2⟩ := klein43 ih
  have fA := hg_frame ih 2 0 (by omega) (by omega) (by omega)
    (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))) (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))))
    (fun j hj => by rcases j with _ | _ | _ | j <;> simp [ctlOr, ctlAt, blackOn] <;> omega)
    (fun j hj => by rcases j with _ | _ | _ | j <;> simp [ctlOr, ctlAt, blackOn] <;> omega)
  have fA2 := hg_frame ih 2 1 (by omega) (by omega) (by omega)
    (ctlOr (ctlAt 0 true) (blackOn 3 (M + 3))) (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))))
    (fun j hj => by rcases j with _ | _ | _ | j <;> simp [ctlOr, ctlAt, blackOn] <;> omega)
    (fun j hj => by rcases j with _ | _ | _ | j <;> simp [ctlOr, ctlAt, blackOn] <;> omega)
  have hb : Derivable (theory (M + 3)) (P43 M * Ab43 M * P43 M) (A2b M) := by
    refine (dright _ (dleft _ fA)).trans ?_
    have e : P43 M * (ppAt (M + 3) 2 0 * B2b M * ppAt (M + 3) 2 0) * P43 M =
        (P43 M * ppAt (M + 3) 2 0) * B2b M * (ppAt (M + 3) 2 0 * P43 M) := by simp only [mul_assoc]
    rw [e]
    exact (dmul (dmul k2 (Derivable.refl _)) k1).trans fA2.symm
  refine conjP_colour U3_inv U3_P ?_ ?_ hb
  · exact colr43 _ D.N15.S6_nodup .hg [2, 0] _ _ (fun j hj => by
      have := D.N15.mem_S6.1 hj
      exact ⟨this.2, by simp; omega, by simp [ctlOr, ctlAt, blackOn]; omega⟩) (fun j hj => by
        by_cases hjw : j ∈ D.N15.S6 M
        · have := D.N15.mem_S6.1 hjw; rw [if_pos hjw]; simp [ctlOr, ctlAt, colOn]; omega
        · rw [if_neg hjw]; have : j < 3 := by by_contra h; exact hjw (D.N15.mem_S6.2 ⟨by omega, hj⟩)
          have h3 : ¬ 3 ≤ j := by omega
          simp [ctlOr, ctlAt, colOn, blackOn, h3])
  · exact colr43 _ D.N15.S6_nodup .hg [2, 1] _ _ (fun j hj => by
      have := D.N15.mem_S6.1 hj
      exact ⟨this.2, by simp; omega, by simp [ctlOr, ctlAt, blackOn]; omega⟩) (fun j hj => by
        by_cases hjw : j ∈ D.N15.S6 M
        · have := D.N15.mem_S6.1 hjw; rw [if_pos hjw]; simp [ctlOr, ctlAt, colOn]; omega
        · rw [if_neg hjw]; have : j < 3 := by by_contra h; exact hjw (D.N15.mem_S6.2 ⟨by omega, hj⟩)
          have h3 : ¬ 3 ≤ j := by omega
          simp [ctlOr, ctlAt, colOn, blackOn, h3])


/-! ### `Bg = R R`, and `R A'' = A'' Ri` ((333), (334)) -/

theorem rr43 : Derivable (theory (M + 3)) (R43 M * R43 M) (Bg43 M) := by
  have h := rot_sq ih true (t := 1) (s := 1) (by omega)
  rwa [Net.mc_congr _ _ _ ctl_1_1, Net.mc_congr _ _ _ ctl_1_1] at h

/-- Conjugation by the swap of the wires `0, 1`. -/
theorem sw0_43 (K : Kind) (tg tg' : List ℕ) (c d : ℕ → Option Bool) (hl : tg.length = kindSp K)
    (hnd : tg.Nodup) (hlt : ∀ t ∈ tg, t < M + 3) (htg : tg.map (Net.tau 0) = tg')
    (hcd : ∀ j < M + 3, d j = c (Net.tau 0 j)) :
    Derivable (theory (M + 3)) (swAt (M + 3) 0 * mc (M + 3) K tg c * swAt (M + 3) 0)
      (mc (M + 3) K tg' d) := by
  have h := D.N15.mcSwapAll' ih 0 (by omega) K tg c hl hnd hlt
  rw [D.N15.conj3, htg] at h
  exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hcd j hj).symm)))

section Black

variable (M) in
abbrev Rb43 : Circ (M + 3) := mc (M + 3) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))
variable (M) in
abbrev Rib43 : Circ (M + 3) := mc (M + 3) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))
variable (M) in
abbrev B0b43 : Circ (M + 3) := mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (blackOn 2 (M + 3)))

theorem swH43 : Derivable (theory (M + 3)) (swAt (M + 3) 0 *
    mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))) * swAt (M + 3) 0) (A2b M) :=
  sw0_43 ih .hg [2, 0] [2, 1] _ _ rfl (by simp) (by intro t ht; simp at ht; omega)
    (by simp [Net.tau]) (fun j hj => by ctl43)

theorem swB43 : Derivable (theory (M + 3)) (swAt (M + 3) 0 *
    mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) * swAt (M + 3) 0) (B0b43 M) :=
  sw0_43 ih .box [1] [0] _ _ rfl (by simp) (by simp) (by simp [Net.tau]) (fun j hj => by ctl43)

theorem rb334 : Derivable (theory (M + 3)) (Rb43 M) (drawn [B0b43 M, A2b M, B0b43 M, A2b M]) := by
  have hS := swsw (M + 3) 0 (by omega)
  have fZ := sw0_43 ih .xz [0] [1] (blackOn 1 (M + 3)) (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))
    rfl (by simp) (by simp) (by simp [Net.tau]) (fun j hj => by ctl43)
  have k := D.N15.via_conj hS (l := [_]) (L := [Rb43 M]) (List.Forall₂.cons fZ List.Forall₂.nil)
    (List.Forall₂.cons (swB43 ih) (List.Forall₂.cons (swH43 ih) (List.Forall₂.cons (swB43 ih)
      (List.Forall₂.cons (swH43 ih) List.Forall₂.nil))))
    (by rw [D.N15.drawn_one']; exact D.eq334 (M + 3) (by omega) ih)
  rwa [D.N15.drawn_one'] at k

theorem rib333 : Derivable (theory (M + 3)) (Rib43 M) (drawn [A2b M, B0b43 M, A2b M, B0b43 M]) := by
  have hS := swsw (M + 3) 0 (by omega)
  have fZ := sw0_43 ih .zx [0] [1] (blackOn 1 (M + 3)) (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))
    rfl (by simp) (by simp) (by simp [Net.tau]) (fun j hj => by ctl43)
  have k := D.N15.via_conj hS (l := [_]) (L := [Rib43 M]) (List.Forall₂.cons fZ List.Forall₂.nil)
    (List.Forall₂.cons (swH43 ih) (List.Forall₂.cons (swB43 ih) (List.Forall₂.cons (swH43 ih)
      (List.Forall₂.cons (swB43 ih) List.Forall₂.nil))))
    (by rw [D.N15.drawn_one']; exact D.eq333 (M + 3) (by omega) ih)
  rwa [D.N15.drawn_one'] at k

/-- (316) in the frame `[2, 1]`: `X` on the box wire `2` passes `A''`. -/
theorem x2_a2 : D.Comm (M + 3) (xAt (M + 3) 2) (A2b M) := by
  have hnd : [2, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1] 1 = 1 := frm_getD hnd hps (by simp)
  have hX : Derivable (theory (M + 3)) (placedBy (M + 3) (netOf [2, 1]) (xAt (M + 3) 0)) (xAt (M + 3) 2) := by
    have := placedBy_xAt (netOf [2, 1]) (netOf_ok hnd hps) 0
    rwa [show pos (netOf [2, 1]).reverse 0 = 2 from f0] at this
  have fH := D.N15.frameAt' ih hnd hps .hg [0, 1] [2, 1] (ctlOr (ctlAt 0 true) (blackOn 3 (M + 3)))
    (blackOn 2 (M + 3)) rfl (by simp) (by intro t ht; simp at ht; omega) (by simp [f0, f1])
    (fun j hj => by
      rcases j with _ | _ | j
      · simp [f0, ctlOr, ctlAt, blackOn]
      · simp [f1, ctlOr, ctlAt, blackOn]
      · obtain ⟨hm, hl⟩ := D.N15.frm_out' hnd hps (j := j + 2) (by simp) hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
        by_cases h0 : frm [2, 1] (j + 2) = 0
        · rw [h0]; simp [ctlOr, ctlAt, blackOn]; omega
        · have h3 : 3 ≤ frm [2, 1] (j + 2) := by omega
          simp [ctlOr, ctlAt, blackOn, h0, h3, hl]; omega)
  exact D.N15.comm_frame hnd hps hX fH (D.eq316 (M + 3) (by omega) ih)

end Black

omit ih in
/-- `X` on the wire `2` then on the wires `3, …`: the black equation becomes the
white one. -/
theorem colour43 {l r : List (Circ (M + 3))} {l₁ r₁ L R : List (Circ (M + 3))}
    (h : Derivable (theory (M + 3)) (drawn l) (drawn r))
    (hl₁ : List.Forall₂ (fun A B => Derivable (theory (M + 3)) (xAt (M + 3) 2 * A * xAt (M + 3) 2) B) l l₁)
    (hr₁ : List.Forall₂ (fun A B => Derivable (theory (M + 3)) (xAt (M + 3) 2 * A * xAt (M + 3) 2) B) r r₁)
    (hL : List.Forall₂ (fun A B => Derivable (theory (M + 3)) (U3 M * A * U3 M) B) l₁ L)
    (hR : List.Forall₂ (fun A B => Derivable (theory (M + 3)) (U3 M * A * U3 M) B) r₁ R) :
    Derivable (theory (M + 3)) (drawn L) (drawn R) :=
  D.N15.via_conj U3_inv hL hR (D.N15.via_conj (D.xx (M + 3) 2 (by omega)) hl₁ hr₁ h)

omit ih in
/-- `X₂` on a black control on wire `2` ((81)). -/
theorem x2_81 (K : Kind) (tg : List ℕ) (c d : ℕ → Option Bool) (h2 : 2 ∉ tg) (hc : c 2 = some true)
    (hd : ∀ j < M + 3, d j = setCtl c 2 (some false) j) :
    Derivable (theory (M + 3)) (xAt (M + 3) 2 * mc (M + 3) K tg c * xAt (M + 3) 2) (mc (M + 3) K tg d) := by
  have h := D.eq81 (M + 3) K tg c 2 true (by omega) h2 hc
  rw [D.N15.conj3] at h
  exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hd j hj).symm)))

omit ih in
/-- `X` on the wires `3, …` on black controls there. -/
theorem u3_col (K : Kind) (tg : List ℕ) (htg : ∀ t ∈ tg, t < 3) (c d : ℕ → Option Bool)
    (hc : ∀ j, 3 ≤ j → j < M + 3 → c j = some true)
    (hd : ∀ j < M + 3, d j = if 3 ≤ j then some false else c j) :
    Derivable (theory (M + 3)) (U3 M * mc (M + 3) K tg c * U3 M) (mc (M + 3) K tg d) :=
  colr43 _ D.N15.S6_nodup K tg c d (fun j hj => by
    have := D.N15.mem_S6.1 hj
    exact ⟨this.2, fun h => by have := htg j h; omega, hc j this.1 this.2⟩) (fun j hj => by
      rw [hd j hj]
      by_cases h3 : 3 ≤ j
      · rw [if_pos h3, if_pos (D.N15.mem_S6.2 ⟨h3, hj⟩)]
      · rw [if_neg h3, if_neg (fun h => h3 (D.N15.mem_S6.1 h).1)])

theorem ra43 : Derivable (theory (M + 3)) (R43 M * A2w M) (A2w M * Ri43 M) := by
  have hX2 := D.xx (M + 3) 2 (by omega)
  have fA : Derivable (theory (M + 3)) (xAt (M + 3) 2 * A2b M * xAt (M + 3) 2) (A2b M) :=
    D.N15.conj_of_comm hX2 (x2_a2 ih).symm
  have fR := x2_81 (M := M) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) (cR43 M) (by simp)
    (by simp [ctlOr, ctlAt, blackOn] <;> omega) (fun j _ => rfl)
  have fRi := x2_81 (M := M) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) (cR43 M) (by simp)
    (by simp [ctlOr, ctlAt, blackOn] <;> omega) (fun j _ => rfl)
  have fB := x2_81 (M := M) .box [0] (ctlOr (ctlAt 1 true) (blackOn 2 (M + 3))) (cB43 M) (by simp)
    (by simp [ctlOr, ctlAt, blackOn] <;> omega) (fun j _ => rfl)
  have gR := u3_col (M := M) .xz [1] (by simp) (cR43 M) (ctlOr (ctlAt 0 true) (W2 M))
    (fun j h3 hj => by ctl43) (fun j hj => by ctl43)
  have gRi := u3_col (M := M) .zx [1] (by simp) (cR43 M) (ctlOr (ctlAt 0 true) (W2 M))
    (fun j h3 hj => by ctl43) (fun j hj => by ctl43)
  have gB := u3_col (M := M) .box [0] (by simp) (cB43 M) (ctlOr (ctlAt 1 true) (W2 M))
    (fun j h3 hj => by ctl43) (fun j hj => by ctl43)
  have gA := u3_col (M := M) .hg [2, 1] (by simp) (ctlOr (ctlAt 0 true) (blackOn 3 (M + 3)))
    (ctlOr (ctlAt 0 true) (W3 M))
    (fun j h3 hj => by ctl43) (fun j hj => by ctl43)
  have k1 := colour43 (l := [Rb43 M]) (r := [B0b43 M, A2b M, B0b43 M, A2b M])
    (by rw [D.N15.drawn_one']; exact rb334 ih) (List.Forall₂.cons fR List.Forall₂.nil)
    (List.Forall₂.cons fB (List.Forall₂.cons fA (List.Forall₂.cons fB (List.Forall₂.cons fA
      List.Forall₂.nil))))
    (List.Forall₂.cons gR List.Forall₂.nil)
    (List.Forall₂.cons gB (List.Forall₂.cons gA (List.Forall₂.cons gB (List.Forall₂.cons gA
      List.Forall₂.nil))))
  have k2 := colour43 (l := [Rib43 M]) (r := [A2b M, B0b43 M, A2b M, B0b43 M])
    (by rw [D.N15.drawn_one']; exact rib333 ih) (List.Forall₂.cons fRi List.Forall₂.nil)
    (List.Forall₂.cons fA (List.Forall₂.cons fB (List.Forall₂.cons fA (List.Forall₂.cons fB
      List.Forall₂.nil))))
    (List.Forall₂.cons gRi List.Forall₂.nil)
    (List.Forall₂.cons gA (List.Forall₂.cons gB (List.Forall₂.cons gA (List.Forall₂.cons gB
      List.Forall₂.nil))))
  rw [D.N15.drawn_one', D.N15.drawn_four'] at k1 k2
  refine (dright _ k1).trans ((der_of_eq ?_).trans (dleft _ k2.symm))
  simp only [mul_assoc]

/-! ### The other pieces -/

/-- (349) in the frame `[2, 1]`: `A''` passes the `ZX` white on wire `0`. -/
theorem a2_zw43 : D.Comm (M + 3) (A2w M) (Zw43 M) := by
  have hnd : [2, 1].Nodup := by decide
  have hps : ∀ p ∈ [2, 1], p < M + 3 := by intro p hp; simp at hp; omega
  have f0 : frm [2, 1] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1] 1 = 1 := frm_getD hnd hps (by simp)
  set x : ℕ → Bool := fun j => decide (frm [2, 1] j = 0)
  obtain ⟨hj0, hj0N⟩ := D.N15.pos_ge hnd hps (w := 0) (by omega) (by simp)
  have hx0 : x (pos (netOf [2, 1]) 0) = true := by simp [x, frm_pos]
  have hxy : DiffOn 2 (M + 3) x (fun _ => false) :=
    ⟨pos (netOf [2, 1]) 0, by simpa using hj0, hj0N, by simp [hx0]⟩
  have hout : ∀ j, 2 ≤ j → j < M + 3 → frm [2, 1] j = 0 ∨ 3 ≤ frm [2, 1] j ∧ frm [2, 1] j < M + 3 := by
    intro j h2 hj
    obtain ⟨hm, hl⟩ := D.N15.frm_out' hnd hps (j := j) (by simpa using h2) hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    omega
  have fH := D.N15.frameAt' ih hnd hps .hg [0, 1] [2, 1] (ctlOr (ctlAt 0 true) (W3 M))
    (colOn 2 (M + 3) x) rfl (by simp) (by intro t ht; simp at ht; omega) (by simp [f0, f1])
    (fun j hj => by
      rcases j with _ | _ | j
      · simp [f0, ctlOr, ctlAt, colOn]
      · simp [f1, ctlOr, ctlAt, colOn]
      · rcases hout (j + 2) (by omega) hj with h | h
        · simp [x, h, ctlOr, ctlAt, colOn, hj]
        · have h0 : frm [2, 1] (j + 2) ≠ 0 := by omega
          simp [x, h0, ctlOr, ctlAt, colOn, hj, h.1, h.2])
  have fZ := D.N15.frameAt' ih hnd hps (Kind.sgnZX false) [1] [1] (ctlOr (ctlAt 0 false) (W2 M))
    (ctlOr (ctlAt 0 false) (colOn 2 (M + 3) fun _ => false)) (by simp [D.N15.kindSp_sgnZX])
    (by simp) (by simp) (by simp [f1])
    (fun j hj => by
      rcases j with _ | _ | j
      · simp [f0, ctlOr, ctlAt, colOn]
      · simp [f1, ctlOr, ctlAt, colOn]
      · rcases hout (j + 2) (by omega) hj with h | h
        · simp [h, ctlOr, ctlAt, colOn, hj]
        · have h0 : frm [2, 1] (j + 2) ≠ 0 := by omega
          have h2 : 2 ≤ frm [2, 1] (j + 2) := by omega
          simp [h0, ctlOr, ctlAt, colOn, hj, h2, h.2])
  exact D.N15.comm_frame hnd hps fH fZ (D.eq349 (M + 3) (by omega) ih x (fun _ => false) hxy false false)

theorem inv43 : Derivable (theory (M + 3)) (Xw43 M * Zw43 M) 1 := by
  have h := rot_inv ih false (t := 1) (s := 0) (by omega)
  rwa [Net.mc_congr _ _ _ ctl_0_1, Net.mc_congr _ _ _ ctl_0_1] at h

omit ih in
theorem setW2n : ∀ j < M + 3, setCtl (W2 M) 0 none j = W2 M j := by
  intro j hj; rcases j with _ | j <;> simp [setCtl, colOn]

/-- (354): the `XZ` (resp. `ZX`) black and white on wire `0` merge. -/
theorem merge43 (a b : Bool) : Derivable (theory (M + 3))
    (mc (M + 3) (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 (!b)) (W2 M)) *
      mc (M + 3) (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 b) (W2 M)))
    (mc (M + 3) (Kind.sgnZX a) [1] (W2 M)) := by
  have h := mergeAtZ ih a (t := 1) (by omega) (W2 M) (by simp [colOn]) (w := 0) (by omega) (by omega) b
  rw [drawn_two, Net.mc_congr _ _ _ (setW2 b), Net.mc_congr _ _ _ (setW2 (!b)),
    Net.mc_congr _ _ _ setW2n] at h
  exact h

/-- (360) with white controls. -/
theorem p360w : Derivable (theory (M + 3)) (P43 M * Xi43 M * P43 M) (Zi43 M) ∧
    Derivable (theory (M + 3)) (P43 M * Zi43 M * P43 M) (Xi43 M) := by
  have h360 := D.eq360 (M + 3) (by omega) ih
  rw [drawn_two, drawn_two] at h360
  have hP := pp_inv44 ih
  set Xb := mc (M + 3) .xz [1] (blackOn 2 (M + 3))
  set Zb := mc (M + 3) .zx [1] (blackOn 2 (M + 3))
  have a1 : Derivable (theory (M + 3)) (P43 M * Xb * P43 M) Zb := by
    refine (dright _ h360.symm).trans ?_
    rw [mul_assoc]; have := dleft Zb hP; rwa [mul_one] at this
  have a2 : Derivable (theory (M + 3)) (P43 M * Zb * P43 M) Xb := by
    rw [mul_assoc]
    refine (dleft _ h360).trans ?_
    rw [← mul_assoc]; have := dright Xb hP; rwa [one_mul] at this
  have col : ∀ K : Kind, Derivable (theory (M + 3)) (U2 M * mc (M + 3) K [1] (blackOn 2 (M + 3)) * U2 M)
      (mc (M + 3) K [1] (W2 M)) := fun K =>
    colr43 _ D.N15.S8_nodup K [1] _ _ (fun j hj => by
      have := D.N15.mem_S8.1 hj
      exact ⟨this.2, by simp; omega, by simp [blackOn]; omega⟩) (fun j hj => by
        by_cases hjw : j ∈ D.N15.S8 M
        · have := D.N15.mem_S8.1 hjw; rw [if_pos hjw]; simp [colOn]; omega
        · rw [if_neg hjw]; have : j < 2 := by by_contra h; exact hjw (D.N15.mem_S8.2 ⟨by omega, hj⟩)
          have h2 : ¬ 2 ≤ j := by omega
          simp [colOn, blackOn, h2])
  exact ⟨conjP_colour U2_inv U2_P (col .xz) (col .zx) a1, conjP_colour U2_inv U2_P (col .zx) (col .xz) a2⟩

/-- (338) under the swap of the wires `1, 2`: `B0` passes `A`. -/
theorem b0_a43 : D.Comm (M + 3) (B043 M) (A43 M) := by
  set x : ℕ → Bool := fun j => decide (j = 2)
  have h := D.eq338 (M + 3) (by omega) ih x x false
  have hS := swsw (M + 3) 1 (by omega)
  have hc := D.N13.Comm.conj h hS (u := swAt (M + 3) 1) (v := swAt (M + 3) 1)
  have hsw := D.N15.mcSwapAll' ih
  refine D.N13.Comm.congr ?_ ?_ hc
  · have h1 := hsw 1 (by omega) .box [0] (ctlOr (ctlAt 1 false) (colOn 2 (M + 3) x)) rfl (by simp)
      (by simp)
    rw [D.N15.conj3] at h1
    refine h1.trans (der_of_eq ?_)
    rw [show ([0] : List ℕ).map (Net.tau 1) = [0] by simp [Net.tau]]
    exact Net.mc_congr _ _ _ (fun j hj => by simp only [x]; ctl43)
  · have h1 := hsw 1 (by omega) .hg [1, 0] (colOn 2 (M + 3) x) rfl (by simp) (by simp)
    rw [D.N15.conj3] at h1
    refine h1.trans (der_of_eq ?_)
    rw [show ([1, 0] : List ℕ).map (Net.tau 1) = [2, 0] by simp [Net.tau]]
    exact Net.mc_congr _ _ _ (fun j hj => by simp only [x]; ctl43)

theorem b0_box43 : Derivable (theory (M + 3)) (B043 M * B043 M) 1 := by
  have h := box_inv ih (t := 0) (s := 3) (by omega)
  rw [drawn_two, Net.mc_congr _ _ _ ctl_3_0] at h
  exact h

theorem b0_rot43 (γ : Bool) (s : ℕ) (hs : s < 2) :
    Derivable (theory (M + 3)) (B043 M * mc (M + 3) (Kind.sgnZX γ) [1] (ctlOf s 1) * B043 M)
      (mc (M + 3) (Kind.sgnZX !γ) [1] (ctlOf s 1)) := by
  have h := box_inv_rot ih γ (t := 1) (w := 0) (s := s) (s' := 3) (by omega) (by omega) (by omega)
    (fun j h1 h0 => by
      rw [bitOf_small (show s < 2 ^ j by
          calc s < 2 ^ 1 := by omega
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)),
        bitOf_small (show 3 < 2 ^ j by
          calc 3 < 2 ^ 2 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega))])
  rwa [Net.mc_congr _ _ _ ctl_3_0] at h

/-! ### The algebra -/

omit ih in
theorem alg43 {Q : Type*} [Monoid Q] {P G A A2 Bg R Ri Xw Zw Xi Zi B0 Y : Q}
    (hP : P * P = 1) (hG : P * G * P = Bg) (hA : P * A * P = A2) (hRR : R * R = Bg)
    (hRA : R * A2 = A2 * Ri) (hc : A2 * Zw = Zw * A2) (hinv : Xw * Zw = 1) (hm1 : R * Xw = Xi)
    (hm2 : Zw * Ri = Zi) (hm3 : Xw * R = Xi) (hPX : P * Xi * P = Zi) (hPZ : P * Zi * P = Xi)
    (hBA : B0 * A = A * B0) (hBG : B0 * G = G * B0) (hB0 : B0 * B0 = 1) (hBZ : B0 * Zw * B0 = Xw)
    (hBR : B0 * Ri * B0 = R) (hY : Y = Xi * B0) :
    G * A = Y * (A * Y) := by
  have conjP : ∀ X : Q, X = P * (P * X * P) * P := fun X => by
    calc X = (P * P) * X * (P * P) := by rw [hP, one_mul, mul_one]
      _ = P * (P * X * P) * P := by simp only [mul_assoc]
  have h2 : Bg * A2 = Xi * A2 * Zi := by
    calc Bg * A2 = R * (R * A2) := by rw [← hRR, mul_assoc]
      _ = R * (A2 * Ri) := by rw [hRA]
      _ = R * ((Xw * Zw) * (A2 * Ri)) := by rw [hinv, one_mul]
      _ = (R * Xw) * ((Zw * A2) * Ri) := by simp only [mul_assoc]
      _ = (R * Xw) * ((A2 * Zw) * Ri) := by rw [hc]
      _ = (R * Xw) * A2 * (Zw * Ri) := by simp only [mul_assoc]
      _ = Xi * A2 * Zi := by rw [hm1, hm2]
  have h3 : G * A = Zi * A * Xi := by
    calc G * A = P * (P * G * P) * P * (P * (P * A * P) * P) := by rw [← conjP, ← conjP]
      _ = P * Bg * (P * P) * A2 * P := by rw [hG, hA]; simp only [mul_assoc]
      _ = P * (Bg * A2) * P := by rw [hP, mul_one]; simp only [mul_assoc]
      _ = P * (Xi * A2 * Zi) * P := by rw [h2]
      _ = P * Xi * (P * P) * A2 * (P * P) * Zi * P := by
          rw [hP, mul_one, mul_one]; simp only [mul_assoc]
      _ = (P * Xi * P) * (P * A2 * P) * (P * Zi * P) := by simp only [mul_assoc]
      _ = Zi * A * Xi := by rw [hPX, hPZ, ← hA, ← conjP]
  have hBZi : B0 * Zi * B0 = Xi := by
    calc B0 * Zi * B0 = B0 * Zw * (B0 * B0) * Ri * B0 := by rw [← hm2, hB0, mul_one]; simp only [mul_assoc]
      _ = (B0 * Zw * B0) * (B0 * Ri * B0) := by simp only [mul_assoc]
      _ = Xi := by rw [hBZ, hBR, hm3]
  have eY : Y = B0 * Zi := by
    calc Y = (B0 * Zi * B0) * B0 := by rw [hY, hBZi]
      _ = B0 * Zi := by rw [mul_assoc, hB0, mul_one]
  have e1 : Y * (A * Y) = B0 * (Zi * A * Xi) * B0 := by
    calc Y * (A * Y) = (B0 * Zi) * (A * (Xi * B0)) := by rw [← eY, ← hY]
      _ = B0 * (Zi * A * Xi) * B0 := by simp only [mul_assoc]
  rw [e1, ← h3]
  calc G * A = G * (B0 * B0) * A := by rw [hB0, mul_one]
    _ = (G * B0) * (B0 * A) := by simp only [mul_assoc]
    _ = (B0 * G) * (A * B0) := by rw [hBG, hBA]
    _ = B0 * (G * A) * B0 := by simp only [mul_assoc]

end Rule43


theorem patt_3245 {n : ℕ} (hn : 3 ≤ n) : patt n 3 2 4 5 = some (2, 2, 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  unfold patt
  rw [show m + 3 = 3 + m by omega, List.range_add, List.findSome?_append]
  rfl

/-- `D(H_[3,2]H_[4,5])`: the multi-controlled `H` on wire `0` with box wire `2`,
black on `1`, white above. -/
theorem dec_3245 {M : ℕ} : dec (M + 3) (Hh (M + 3) 3 2 4 5) = A43 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_Hh (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    if_pos (by unfold Distinct4; omega)]
  simp only [dHH4, patt_3245 (by omega : 3 ≤ M + 3)]
  simp only [show ¬ (2 = 1) by omega, if_false]
  show colour (M + 1 + 2) (placeAt2 (M + 1 + 2) (stdMch (M + 1 + 2)) 0 2) (bitOf (gray 3))
    (fun j => j == 2 || j == 0) = _
  rw [placeAt2_mc (M + 1) (gray 3) 2 0 (by omega) (by omega) (by omega), show gray 3 = 2 by decide]
  refine Net.mc_congr _ _ _ (fun j hj => ?_)
  rcases j with _ | _ | _ | j
  · simp [ctl2Of, ctlOr, ctlAt, colOn]
  · simp [ctl2Of, ctlOr, ctlAt, colOn, bitOf]
  · simp [ctl2Of, ctlOr, ctlAt, colOn]
  · simp [ctl2Of, ctlOr, ctlAt, colOn, hj, bitOf_small (show 2 < 2 ^ (j + 3) by
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega))]

/-- (43) decodes to the chain of this file. -/
theorem dec43 {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Hh (M + 3) 0 1 3 2, Hh (M + 3) 3 2 4 5]))
      (decW (M + 3) (wordOf [Xx (M + 3) 0 3 1 2, Hh (M + 3) 3 2 4 5, Xx (M + 3) 0 3 1 2])) := by
  have h361 := D.eq361 (M + 3) (by omega) ih
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one] at h361 ⊢
  rw [dec_0132 (by omega : 3 ≤ M + 3), gadget_colOn, dec_3245]
  rw [drawn_two] at h361
  have hbz := b0_rot43 ih false 0 (by omega)
  rw [Net.mc_congr _ _ _ ctl_0_1, Net.mc_congr _ _ _ ctl_0_1] at hbz
  have hbr := b0_rot43 ih false 1 (by omega)
  rw [Net.mc_congr _ _ _ ctl_1_1, Net.mc_congr _ _ _ ctl_1_1] at hbr
  obtain ⟨hpx, hpz⟩ := p360w ih
  have key := alg43 (Q := (conGen (theory (M + 3))).Quotient)
    (P := (P43 M : (conGen (theory (M + 3))).Quotient)) (G := G43 M) (A := A43 M) (A2 := A2w M)
    (Bg := Bg43 M) (R := R43 M) (Ri := Ri43 M) (Xw := Xw43 M) (Zw := Zw43 M) (Xi := Xi43 M)
    (Zi := Zi43 M) (B0 := B043 M) (Y := dec (M + 3) (Xx (M + 3) 0 3 1 2))
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 (pp_inv44 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (g_pp43 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (a_pp43 ih))
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 (rr43 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (ra43 ih))
    (by
      have h := a2_zw43 ih
      unfold D.Comm at h; rw [drawn_two, drawn_two] at h
      rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 h.symm)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 (inv43 ih))
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 (merge43 ih true false))
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 (merge43 ih false true))
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 (merge43 ih true true))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hpx)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hpz)
    (by
      have h := b0_a43 ih
      unfold D.Comm at h; rw [drawn_two, drawn_two] at h
      rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 h.symm)
    (by
      have h := D.eq338 (M + 3) (by omega) ih (fun _ => false) (fun _ => false) true
      unfold D.Comm at h; rw [drawn_two, drawn_two] at h
      rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 h.symm)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 (b0_box43 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hbz)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hbr)
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 h361)
  apply (Con.eq _).1
  simp only [Con.coe_mul]
  exact key

end QCert.RealCliffordCH.Sec8.E
