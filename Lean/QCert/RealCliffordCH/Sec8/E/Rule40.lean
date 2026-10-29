/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (40)

`D((-1)_[3](-1)_[4])` is the box `Bw` on wire `2` (black on `1`, white on `0`
and above), `D((-1)_[2]X_[2,3])` the `ZX` on wire `0` (black on `1`, white
above) and `D(H_[0,1]H_[3,2])` the gadget `Hg`.  The paper's chain:

* (333) with its controls exchanged by (353), coloured by (81) and (315):
  the `ZX` is `Hg Bb Hg Bb`, `Bb` the box on wire `2` black on `0`, `1`;
* (309): `Bb Bw = Bi`, the box on wire `2` with wire `0` idle;
* `Bi` passes `Hg`: its box wire moves to wire `0` ((274)), where (309) splits
  it into two boxes passing `Hg` by (338);
* (312), (311).

Every step was checked numerically at `N = 3, …, 6` (scratch `m40.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule38

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## `X` moved along a network, and `X` on the box wire -/

section XBox

variable {N : ℕ}

theorem placedBy_xAt : ∀ (μ : List ℕ), Ok N μ → ∀ q,
    Derivable (theory N) (placedBy N μ (xAt N q)) (xAt N (pos μ.reverse q))
  | [], _, q => by rw [placedBy_nil]; exact Derivable.refl _
  | j :: μ, hμ, q => by
    rw [placedBy_cons, drawn3, List.reverse_cons, pos_append, pos_cons, pos_nil]
    exact (dctx _ _ (placedBy_xAt μ (fun k hk => hμ k (by simp [hk])) q)).trans
      (x_conj N j _ (hμ j (by simp)))

/-- (315) with any colours: `X` on the box wire passes the box. -/
theorem xbox0 (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    D.Comm N (xAt N 0) (mc N .box [0] (colOn 1 N x)) := by
  set ws := (List.range N).filter (fun j => decide (1 ≤ j) && !x j) with hws
  have hnd : ws.Nodup := List.nodup_range.filter _
  have hmem : ∀ j ∈ ws, j < N ∧ j ∉ [0] ∧ blackOn 1 N j = some true := by
    intro j hj
    obtain ⟨hjN, hp⟩ := List.mem_filter.1 hj
    have hp' : 1 ≤ j ∧ x j = false := by simpa using hp
    have hjN' := List.mem_range.1 hjN
    exact ⟨hjN', by simp; omega, by simp [blackOn]; omega⟩
  have hc := D.N13.mc_colour N .box [0] (blackOn 1 N) ws hnd hmem
  have e : mc N .box [0] (fun j => if j ∈ ws then some false else blackOn 1 N j) =
      mc N .box [0] (colOn 1 N x) := by
    apply Net.mc_congr
    intro j hj
    by_cases h1 : 1 ≤ j
    · cases hx : x j
      · have : j ∈ ws := by simp [hws, hj, h1, hx]
        simp [this, colOn, h1, hj, hx]
      · have : j ∉ ws := by simp [hws, hx]
        simp [this, colOn, blackOn, h1, hj, hx]
    · have : j ∉ ws := by simp [hws, h1]
      simp [this, colOn, blackOn, h1]
  rw [e, Net.colourW_eq] at hc
  set Dw := drawn (ws.map (xAt N))
  have h0 : 0 ∉ ws := fun h => (hmem 0 h).2.1 (by simp)
  have hx : Derivable (theory N) (xAt N 0 * Dw) (Dw * xAt N 0) := x_comm_xs 0 ws h0
  have h315 := D.eq315 N hN ih
  rw [drawn_two, drawn_two] at h315
  have k : D.Comm N (xAt N 0) (Dw * D.Bx N * Dw) := by
    unfold D.Comm
    rw [drawn_two, drawn_two]
    -- `Dw B Dw X = Dw B X Dw = Dw X B Dw = X Dw B Dw`
    have e1 : Dw * D.Bx N * Dw * xAt N 0 = Dw * D.Bx N * (Dw * xAt N 0) := by simp only [mul_assoc]
    have e2 : Dw * (D.Bx N * xAt N 0) * Dw = Dw * D.Bx N * (xAt N 0 * Dw) := by simp only [mul_assoc]
    have e3 : Dw * (xAt N 0 * D.Bx N) * Dw = (Dw * xAt N 0) * D.Bx N * Dw := by simp only [mul_assoc]
    have e4 : xAt N 0 * Dw * D.Bx N * Dw = xAt N 0 * (Dw * D.Bx N * Dw) := by simp only [mul_assoc]
    rw [e1]
    refine (dleft _ hx.symm).trans ?_
    rw [← e2]
    refine (dctx _ _ h315).trans ?_
    rw [e3]
    refine (dright _ (dright _ hx.symm)).trans ?_
    exact der_of_eq e4
  exact D.N13.Comm.congr (Derivable.refl _) hc k

/-- `X` on the box wire passes the box, the box on any wire with a control on
every other wire. -/
theorem xbox (hN : 3 ≤ N) (ih : IH N) {t : ℕ} (ht : t < N) (c : ℕ → Option Bool)
    (hct : c t = none) (hc : ∀ j < N, j ≠ t → (c j).isSome) :
    D.Comm N (xAt N t) (mc N .box [t] c) := by
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < N := by simp [ht]
  have h0 : frm [t] 0 = t := frm_getD hnd hps (by simp)
  set x : ℕ → Bool := fun j => (c (frm [t] j)).getD false
  have hA : Derivable (theory N) (placedBy N (netOf [t]) (xAt N 0)) (xAt N t) := by
    have := placedBy_xAt (netOf [t]) (netOf_ok hnd hps) 0
    rwa [show pos (netOf [t]).reverse 0 = t from h0] at this
  have hB : Derivable (theory N) (placedBy N (netOf [t]) (mc N .box [0] (colOn 1 N x)))
      (mc N .box [t] c) := by
    refine D.N15.frameAt' ih hnd hps .box [0] [t] c (colOn 1 N x) rfl (by simp) (by simp; omega)
      (by simp [h0]) (fun j hj => ?_)
    rcases j with _ | j
    · simp [colOn, h0, hct]
    · have hne : frm [t] (j + 1) ≠ t := by
        intro e; have := frm_injective [t] (e.trans h0.symm); omega
      have hl : frm [t] (j + 1) < N := frm_lt hnd hps hj
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hc _ hl hne)
      simp [colOn, hj, x, hb]
  exact D.N15.comm_frame hnd hps hA hB (xbox0 hN ih x)

end XBox

/-! ## The gates -/

section Gates

variable (M : ℕ)

/-- The gadget. -/
abbrev Hg40 : Circ (M + 3) := mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false)
/-- `D((-1)_[3](-1)_[4])`: the box on wire `2`, black on `1`, white elsewhere. -/
abbrev Bw40 : Circ (M + 3) := mc (M + 3) .box [2] (ctlOf 2 2)
/-- The box on wire `2`, black on `0`, `1`, white above. -/
abbrev Bb40 : Circ (M + 3) := mc (M + 3) .box [2] (ctlOf 3 2)
/-- The box on wire `2`, black on `1`, white above, wire `0` idle. -/
abbrev cI40 : ℕ → Option Bool := ctlOr (ctlAt 1 true) (colOn 3 (M + 3) fun _ => false)
abbrev Bi40 : Circ (M + 3) := mc (M + 3) .box [2] (cI40 M)
/-- `D((-1)_[2]X_[2,3])`: the `ZX` on wire `0`, black on `1`, white above. -/
abbrev Z40 : Circ (M + 3) := mc (M + 3) .zx [0] (ctlOf 3 0)

end Gates

section Rule40

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- (333) with the controls `1`, `2` exchanged and coloured: the `ZX` is
`Hg Bb Hg Bb`. -/
theorem z333 : Derivable (theory (M + 3)) (Z40 M) (drawn [Hg40 M, Bb40 M, Hg40 M, Bb40 M]) := by
  have hsw := D.N15.mcSwapAll' ih
  have E0 := D.eq333 (M + 3) (by omega) ih
  -- the swap of the wires `1, 2`
  have hS1 := swsw (M + 3) 1 (by omega)
  have s1 : ∀ (K : Kind) (tg tg' : List ℕ) (c d : ℕ → Option Bool), tg.length = kindSp K →
      tg.Nodup → (∀ t ∈ tg, t < M + 3) → tg.map (Net.tau 1) = tg' →
      (∀ j < M + 3, d j = c (Net.tau 1 j)) →
      Derivable (theory (M + 3)) (swAt (M + 3) 1 * mc (M + 3) K tg c * swAt (M + 3) 1)
        (mc (M + 3) K tg' d) := by
    intro K tg tg' c d hl hnd hlt htg hcd
    have h := hsw 1 (by omega) K tg c hl hnd hlt
    rw [D.N15.conj3, htg] at h
    exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hcd j hj).symm)))
  set ZXb := mc (M + 3) .zx [0] (blackOn 1 (M + 3))
  set Hgb := mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3))
  set cBb := ctlOr (ctlAt 0 true) (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3)))
  set Bbb := mc (M + 3) .box [2] cBb
  have k1 : Derivable (theory (M + 3)) (drawn [ZXb]) (drawn [Hgb, Bbb, Hgb, Bbb]) := by
    have fZ := s1 .zx [0] [0] (blackOn 1 (M + 3)) (blackOn 1 (M + 3)) rfl (by simp) (by simp)
      (by simp [Net.tau]) (fun j hj => by
        rcases j with _ | _ | _ | j <;> simp [Net.tau, blackOn] <;> omega)
    have fH := s1 .hg [2, 0] [1, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))) (blackOn 2 (M + 3))
      rfl (by simp) (by simp) (by simp [Net.tau]) (fun j hj => by
        rcases j with _ | _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn] <;> omega)
    have fB := s1 .box [1] [2] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) cBb rfl (by simp)
      (by simp) (by simp [Net.tau]) (fun j hj => by
        rcases j with _ | _ | _ | j <;> simp [cBb, Net.tau, ctlOr, ctlAt, blackOn] <;> omega)
    exact D.N15.via_conj hS1 (List.Forall₂.cons fZ List.Forall₂.nil)
      (List.Forall₂.cons fH (List.Forall₂.cons fB (List.Forall₂.cons fH
        (List.Forall₂.cons fB List.Forall₂.nil)))) (by rw [drawn_single]; exact E0)
  -- `X` on wire `2`: (81) for the `ZX` and `Hg`, (315) for the box
  have hX2 := D.xx (M + 3) 2 (by omega)
  have g81 : ∀ (K : Kind) (tg : List ℕ) (c d : ℕ → Option Bool), 2 ∉ tg → c 2 = some true →
      (∀ j < M + 3, d j = setCtl c 2 (some false) j) →
      Derivable (theory (M + 3)) (xAt (M + 3) 2 * mc (M + 3) K tg c * xAt (M + 3) 2)
        (mc (M + 3) K tg d) := by
    intro K tg c d h2 hc hd
    have h := D.eq81 (M + 3) K tg c 2 true (by omega) h2 hc
    rw [D.N15.conj3] at h
    exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hd j hj).symm)))
  set ZX2 := mc (M + 3) .zx [0] (setCtl (blackOn 1 (M + 3)) 2 (some false))
  set Hg2 := mc (M + 3) .hg [1, 0] (setCtl (blackOn 2 (M + 3)) 2 (some false))
  have k2 : Derivable (theory (M + 3)) (drawn [ZX2]) (drawn [Hg2, Bbb, Hg2, Bbb]) := by
    have fZ := g81 .zx [0] (blackOn 1 (M + 3)) (setCtl (blackOn 1 (M + 3)) 2 (some false))
      (by simp) (by simp only [blackOn]; rw [if_pos (by omega)]) (fun j _ => rfl)
    have fH := g81 .hg [1, 0] (blackOn 2 (M + 3)) (setCtl (blackOn 2 (M + 3)) 2 (some false))
      (by simp) (by simp only [blackOn]; rw [if_pos (by omega)]) (fun j _ => rfl)
    have fB : Derivable (theory (M + 3)) (xAt (M + 3) 2 * Bbb * xAt (M + 3) 2) Bbb :=
      D.N15.conj_of_comm hX2 (xbox (by omega) ih (t := 2) (by omega) cBb
        (by simp [cBb, ctlOr, ctlAt, blackOn])
        (fun j hj hj2 => by
          rcases j with _ | _ | _ | j
          · simp [cBb, ctlOr, ctlAt]
          · simp [cBb, ctlOr, ctlAt]
          · exact absurd rfl hj2
          · simp [cBb, ctlOr, ctlAt, blackOn]; omega)).symm
    exact D.N15.via_conj hX2 (List.Forall₂.cons fZ List.Forall₂.nil)
      (List.Forall₂.cons fH (List.Forall₂.cons fB (List.Forall₂.cons fH
        (List.Forall₂.cons fB List.Forall₂.nil)))) k1
  -- `X` on the wires `3, …`
  set ws := (List.range M).map (· + 3) with hws
  have hnd : ws.Nodup := List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
  have mem_ws : ∀ {j : ℕ}, j ∈ ws ↔ 3 ≤ j ∧ j < M + 3 := by
    intro j
    simp only [hws, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro h; exact ⟨j - 3, by omega, by omega⟩
  have hu := D.xs_inv (M + 3) ws hnd (fun w hw => (mem_ws.1 hw).2)
  set u := drawn (ws.map (xAt (M + 3)))
  have colr : ∀ (K : Kind) (tg : List ℕ) (c d : ℕ → Option Bool),
      (∀ j ∈ ws, j ∉ tg ∧ c j = some true) →
      (∀ j < M + 3, d j = if j ∈ ws then some false else c j) →
      Derivable (theory (M + 3)) (u * mc (M + 3) K tg c * u) (mc (M + 3) K tg d) := by
    intro K tg c d hc hd
    have h := D.N13.mc_colour (M + 3) K tg c ws hnd
      (fun j hj => ⟨(mem_ws.1 hj).2, (hc j hj).1, (hc j hj).2⟩)
    rw [Net.colourW_eq] at h
    exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hd j hj).symm)))
  have fZ := colr .zx [0] (setCtl (blackOn 1 (M + 3)) 2 (some false)) (ctlOf 3 0)
    (fun j hj => by
      have := mem_ws.1 hj
      refine ⟨by simp; omega, ?_⟩
      show (if j = 2 then some false else blackOn 1 (M + 3) j) = some true
      rw [if_neg (by omega)]; simp only [blackOn]; rw [if_pos (by omega)])
    (fun j hj => by
      by_cases hjw : j ∈ ws
      · have := mem_ws.1 hjw
        rw [if_pos hjw]
        simp only [ctlOf, bitOf]
        rw [if_neg (by omega)]
        have : 3 >>> j = 0 := by
          rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by
            calc 3 < 2 ^ 3 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this.1)
        simp [this]
      · rw [if_neg hjw]
        have : j < 3 := by by_contra h; exact hjw (mem_ws.2 ⟨by omega, hj⟩)
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp [ctlOf, setCtl, blackOn, bitOf])
  have fH := colr .hg [1, 0] (setCtl (blackOn 2 (M + 3)) 2 (some false)) (colOn 2 (M + 3) fun _ => false)
    (fun j hj => by
      have := mem_ws.1 hj
      refine ⟨by simp; omega, ?_⟩
      show (if j = 2 then some false else blackOn 2 (M + 3) j) = some true
      rw [if_neg (by omega)]; simp only [blackOn]; rw [if_pos (by omega)])
    (fun j hj => by
      by_cases hjw : j ∈ ws
      · have := mem_ws.1 hjw
        rw [if_pos hjw]; simp [colOn]; omega
      · rw [if_neg hjw]
        have : j < 3 := by by_contra h; exact hjw (mem_ws.2 ⟨by omega, hj⟩)
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp [colOn, setCtl, blackOn])
  have fB := colr .box [2] cBb (ctlOf 3 2)
    (fun j hj => by
      have := mem_ws.1 hj
      refine ⟨by simp; omega, ?_⟩
      simp [cBb, ctlOr, ctlAt, blackOn]; omega)
    (fun j hj => by
      by_cases hjw : j ∈ ws
      · have := mem_ws.1 hjw
        rw [if_pos hjw]
        simp only [ctlOf, bitOf]
        rw [if_neg (by omega)]
        have : 3 >>> j = 0 := by
          rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by
            calc 3 < 2 ^ 3 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) this.1)
        simp [this]
      · rw [if_neg hjw]
        have : j < 3 := by by_contra h; exact hjw (mem_ws.2 ⟨by omega, hj⟩)
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;>
          simp [ctlOf, cBb, ctlOr, ctlAt, blackOn, bitOf])
  have k3 := D.N15.via_conj hu (List.Forall₂.cons fZ List.Forall₂.nil)
    (List.Forall₂.cons fH (List.Forall₂.cons fB (List.Forall₂.cons fH
      (List.Forall₂.cons fB List.Forall₂.nil)))) k2
  rwa [drawn_single] at k3

/-- (309): `Bb` then `Bw` is the box with wire `0` idle. -/
theorem merge40 : Derivable (theory (M + 3)) (Bw40 M * Bb40 M) (Bi40 M) := by
  have h := mergeAt ih (t := 2) (by omega) (cI40 M) (by simp [cI40, ctlOr, ctlAt, colOn])
    (w := 0) (by omega) (by omega) true
  have e1 : mc (M + 3) .box [2] (setCtl (cI40 M) 0 (some true)) = Bb40 M :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | _ | j
      · simp [setCtl, ctlOf, bitOf]
      · simp [cI40, setCtl, ctlOr, ctlAt, colOn, ctlOf, bitOf]
      · simp [cI40, setCtl, ctlOr, ctlAt, colOn, ctlOf]
      · have : 3 >>> (j + 3) = 0 := by
          rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by
            calc 3 < 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [cI40, setCtl, ctlOr, ctlAt, colOn, ctlOf, bitOf, this, hj])
  have e2 : mc (M + 3) .box [2] (setCtl (cI40 M) 0 (some !true)) = Bw40 M :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | _ | j
      · simp [setCtl, ctlOf, bitOf]
      · simp [cI40, setCtl, ctlOr, ctlAt, colOn, ctlOf, bitOf]
      · simp [cI40, setCtl, ctlOr, ctlAt, colOn, ctlOf]
      · have : 2 >>> (j + 3) = 0 := by
          rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by
            calc 2 < 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (j + 3) := Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [cI40, setCtl, ctlOr, ctlAt, colOn, ctlOf, bitOf, this, hj])
  have e3 : mc (M + 3) .box [2] (setCtl (cI40 M) 0 none) = Bi40 M :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | j
      · simp [cI40, setCtl, ctlOr, ctlAt, colOn]
      · simp [cI40, setCtl])
  rw [e1, e2, e3, drawn_two] at h
  exact h

/-- `Bi` passes the gadget: (274), (309), (338). -/
theorem bi_hg : D.Comm (M + 3) (Bi40 M) (Hg40 M) := by
  -- (274), coloured, moved by the frame of `[0, 2]`
  have hnd : [0, 2].Nodup := by simp
  have hps : ∀ p ∈ [0, 2], p < M + 3 := by simp
  have g0 : frm [0, 2] 0 = 0 := frm_getD hnd hps (by simp)
  have g1 : frm [0, 2] 1 = 2 := frm_getD hnd hps (by simp)
  set x : ℕ → Bool := fun j => decide (frm [0, 2] j = 1)
  have hd : ∀ j < M + 3, colOn 2 (M + 3) x j = cI40 M (frm [0, 2] j) := by
    intro j hj
    rcases j with _ | _ | j
    · simp [cI40, colOn, g0, ctlOr, ctlAt]
    · simp [cI40, colOn, g1, ctlOr, ctlAt]
    · obtain ⟨hm, hl⟩ := D.N15.frm_out' hnd hps (j := j + 2) (by simp) hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      by_cases h1 : frm [0, 2] (j + 2) = 1
      · simp [cI40, colOn, ctlOr, ctlAt, h1, x, hj]
      · have h3 : 3 ≤ frm [0, 2] (j + 2) := by omega
        simp [cI40, colOn, ctlOr, ctlAt, h1, x, hj, h3, hl]
  have f0 := D.N15.frameAt' ih hnd hps .box [0] [0] (cI40 M) (colOn 2 (M + 3) x) rfl (by simp)
    (by simp) (by simp [g0]) hd
  have f1 := D.N15.frameAt' ih hnd hps .box [1] [2] (cI40 M) (colOn 2 (M + 3) x) rfl (by simp)
    (by simp) (by simp [g1]) hd
  have mv := via_frame hnd hps (List.Forall₂.cons f0 List.Forall₂.nil)
    (List.Forall₂.cons f1 List.Forall₂.nil) (by
      rw [drawn_single, drawn_single]; exact move274 (N := M + 3) x ih (by omega))
  rw [drawn_single, drawn_single] at mv
  -- (309) on wire `2` and (338)
  set y : ℕ → Bool := fun j => decide (j = 1)
  have h309 := D.eq309 (M + 3) (by omega) ih y 2 (by omega) (by omega) true
  have eI : mc (M + 3) .box [0] (setCtl (colOn 1 (M + 3) y) 2 none) = mc (M + 3) .box [0] (cI40 M) :=
    Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | _ | j
      · simp [cI40, setCtl, colOn, ctlOr, ctlAt]
      · simp [cI40, setCtl, colOn, ctlOr, ctlAt, y]
      · simp [cI40, setCtl, colOn, ctlOr, ctlAt]
      · simp [cI40, setCtl, colOn, ctlOr, ctlAt, y, hj])
  have c338 : ∀ b : Bool, D.Comm (M + 3) (mc (M + 3) .box [0] (setCtl (colOn 1 (M + 3) y) 2 (some b)))
      (Hg40 M) := by
    intro b
    have h := D.eq338 (M + 3) (by omega) ih (fun j => decide (j = 2) && b) (fun _ => false) true
    have e : mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) fun j => decide (j = 2) && b)) =
        mc (M + 3) .box [0] (setCtl (colOn 1 (M + 3) y) 2 (some b)) :=
      Net.mc_congr _ _ _ (fun j hj => by
        rcases j with _ | _ | _ | j
        · simp [cI40, setCtl, colOn, ctlOr, ctlAt]
        · simp [cI40, setCtl, colOn, ctlOr, ctlAt, y]
        · simp [cI40, setCtl, colOn, ctlOr, ctlAt]
        · simp [cI40, setCtl, colOn, ctlOr, ctlAt, y, hj])
    rw [e] at h
    exact h
  rw [eI, drawn_two] at h309
  have c1 : D.Comm (M + 3) (mc (M + 3) .box [0] (setCtl (colOn 1 (M + 3) y) 2 (some !true)) *
      mc (M + 3) .box [0] (setCtl (colOn 1 (M + 3) y) 2 (some true))) (Hg40 M) :=
    D.N13.Comm.mul_left (c338 _) (c338 _)
  exact D.N13.Comm.congr (h309.trans mv) (Derivable.refl _) c1

omit ih in
/-- The algebra of the chain. -/
theorem rule40_alg {Q : Type*} [Monoid Q] {z bb bw bi hg : Q} (hz : z = bb * hg * bb * hg)
    (h2 : bw * bb = bi) (h3 : bb * bb = 1) (h4 : hg * hg = 1) (h5 : bi * hg = hg * bi) :
    bw * hg = hg * bw * z := by
  have e1 : hg * bi * hg = bi := by rw [mul_assoc, h5, ← mul_assoc, h4, one_mul]
  have e2 : bi * bb = bw := by rw [← h2, mul_assoc, h3, mul_one]
  calc bw * hg = bi * bb * hg := by rw [e2]
    _ = hg * bi * hg * bb * hg := by rw [e1]
    _ = hg * (bw * bb) * hg * bb * hg := by rw [h2]
    _ = hg * bw * (bb * hg * bb * hg) := by simp only [mul_assoc]
    _ = hg * bw * z := by rw [hz]

end Rule40

/-! ## The decoded letters -/

theorem isOnes_3_2 : IsOnes 3 2 :=
  ⟨fun j hj => by interval_cases j <;> decide, by decide⟩

theorem isOnes_2_0 : IsOnes 2 0 := ⟨fun j hj => absurd hj (by omega), by decide⟩

theorem dec_zz34 {M : ℕ} : dec (M + 3) (Zz (M + 3) 3 4) = Bw40 M := by
  have h8 : 8 ≤ 2 ^ (M + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (M + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8' : 8 ≤ 2 ^ (M + 2 + 1) := h8
  rw [dec_Zz (by omega) (by omega), show dZZ (M + 3) 3 4 = dZZ (M + 3) 3 (3 + 1) from rfl, dZZ_succ,
    dZZ1_mc (M + 2), tOf_eq isOnes_3_2 (by omega), show gray 3 = 2 by decide]

theorem dec_zx223 {M : ℕ} : dec (M + 3) (Zx (M + 3) 2 2 3) = Z40 M := by
  have h8 : 8 ≤ 2 ^ (M + 3) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (M + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8' : 8 ≤ 2 ^ (M + 2 + 1) := h8
  rw [show Zx (M + 3) 2 2 3 = Zx (M + 3) 2 2 (2 + 1) from rfl, dec_Zx_lo (by omega), dZX1_mc (M + 2)]
  have hk : kindZX (M + 2 + 1) 2 0 = .zx := by
    unfold kindZX
    rw [tOf_eq isOnes_2_0 (by omega)]
    have hb : bitOf (gray 2) 0 = 1 := by decide
    simp [hb]
  rw [hk, tOf_eq isOnes_2_0 (by omega), show gray 2 = 3 by decide]

/-- (40) decodes to the chain (333), (309), (274), (338), (312), (311). -/
theorem dec40 {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Zz (M + 3) 3 4, Hh (M + 3) 0 1 3 2]))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 1 3 2, Zz (M + 3) 3 4, Zx (M + 3) 2 2 3])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_0132 (by omega : 3 ≤ M + 3), gadget_colOn, dec_zz34, dec_zx223]
  have h1 := z333 ih
  have h2 := merge40 ih
  have h3 := box_inv ih (t := 2) (s := 3) (by omega)
  rw [drawn_two] at h3
  have h4 := dec41 ih
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_0132 (by omega : 3 ≤ M + 3), gadget_colOn] at h4
  have h5 := bi_hg ih
  unfold D.Comm at h5
  rw [drawn_two, drawn_two] at h5
  rw [D.N15.drawn_four'] at h1
  have key := rule40_alg (Q := (conGen (theory (M + 3))).Quotient)
    (z := (Z40 M : (conGen (theory (M + 3))).Quotient)) (bb := Bb40 M) (bw := Bw40 M)
    (bi := Bi40 M) (hg := Hg40 M)
    (by simp only [← Con.coe_mul]; exact (Con.eq _).2 h1)
    (by rw [← Con.coe_mul]; exact (Con.eq _).2 h2)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 h3)
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 h4)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 h5.symm)
  apply (Con.eq _).1
  simp only [Con.coe_mul]
  exact key.trans (mul_assoc _ _ _)

end QCert.RealCliffordCH.Sec8.E
