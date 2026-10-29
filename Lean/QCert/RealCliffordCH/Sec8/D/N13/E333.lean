/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equations (333) and (334), given (339)

The paper's proof (page 233).  By Definition 2.4 the multi-controlled `ZX`
is `CH · B · CH · B` (`B` the box on wire `1`, all black).  `CH` is the
multi-controlled `H` with its box on wire `2`, its `H` on wire `0` and its
only control on wire `1` (`hg_ch`: two swaps and (f4)), which is, by
(310), the product of the multi-controlled `H` over every colouring of the
wires `3, …` (`merged`).  Every factor but the black one `HG` passes `B`
by (339) (they differ from `B` on a wire `≥ 3`), the factors commute
(340) and are involutions (312), so their product `P` passes `B` and `HG`
and squares to `1`: `B (HG P) B (HG P) = B HG B HG`.

The multi-controlled `H` gates are handled in the frame where they sit on
the wires `0, 1` (`hgR`: the swaps of the wires `0, 1` and `1, 2` carry
`hg[0, 1]` to `hg[2, 0]`), where (310), (312) and (340) are stated.  The
merge (310) with idle wires is `E.MergeHg.mergeHgC`, which cannot be
imported here (it depends on `D.N15`); it is repeated as `mergeHg0`.

(339) is a hypothesis (`h339`), supplied by `N13.eq339`; at three wires it
is vacuous.  (334) follows from (333), (317), (311) and (312).

No window is decided here.  Memory (2026-10-29): about 20 s, peak 0.35 GB
anonymous.
-/
import QCert.RealCliffordCH.Sec8.D.N13.MergeAll
import QCert.RealCliffordCH.Sec8.D.N13.E339a

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- Pointwise equality of control functions on the wires `0, …, 3` and above. -/
macro "ctl_case33" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ 4 ≤ i) with h | h | h | h | h4 <;> (try subst h) <;>
  simp only [colOn, ctlOr, ctlAt, blackOn, setCtl, Net.tau, Function.comp] <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | omega))

/-! ## (310) with idle wires, and over a list of wires -/

theorem merge_step_hg0 {N' : ℕ} (hN : 3 ≤ N' + 1) (ih : IH (N' + 1))
    (down : ∀ c' : ℕ → Option Bool, c' 0 = none → c' 1 = none → ∀ w', 2 ≤ w' → w' < N' →
      ∀ b : Bool, Derivable (theory N')
        (drawn [mc N' .hg [0, 1] (setCtl c' w' (some b)), mc N' .hg [0, 1] (setCtl c' w' (some !b))])
        (mc N' .hg [0, 1] (setCtl c' w' none)))
    (c : ℕ → Option Bool) (hc0 : c 0 = none) (hc1 : c 1 = none) (w : ℕ) (hw1 : 2 ≤ w)
    (hw2 : w < N' + 1) (b : Bool) :
    Derivable (theory (N' + 1))
      (drawn [mc (N' + 1) .hg [0, 1] (setCtl c w (some b)),
        mc (N' + 1) .hg [0, 1] (setCtl c w (some !b))])
      (mc (N' + 1) .hg [0, 1] (setCtl c w none)) := by
  by_cases hq : ∃ q, 2 ≤ q ∧ q < N' + 1 ∧ q ≠ w ∧ c q = none
  · obtain ⟨q, hq1, hq2, hqw, hcq⟩ := hq
    have hA : ∀ v, ToTop N' q (mc (N' + 1) .hg [0, 1] (setCtl c w v))
        (mc N' .hg [0, 1] (setCtl (c ∘ liftW q) (Net.dropW q w) v)) := by
      intro v
      have := ToTop.mc (M := N') (q := q) (by omega) .hg [0, 1] (setCtl c w v) rfl (by simp)
        (by simp; omega) (by simp; omega) (by simp [setCtl, hqw, hcq])
      have e0 : [0, 1].map (Net.dropW q) = [0, 1] := by
        simp [Net.dropW, show 0 < q by omega, show 1 < q by omega]
      rwa [E.setCtl_liftW (Ne.symm hqw), e0] at this
    have hc0' : (c ∘ liftW q) 0 = none := by simp [liftW, show 0 < q by omega, hc0]
    have hc1' : (c ∘ liftW q) 1 = none := by simp [liftW, show 1 < q by omega, hc1]
    have hw' : 2 ≤ Net.dropW q w ∧ Net.dropW q w < N' := by simp only [Net.dropW]; split_ifs <;> omega
    exact liftIdle (ToTop.ofList (List.Forall₂.cons (hA _) (List.Forall₂.cons (hA _)
      List.Forall₂.nil))) (hA none) (down (c ∘ liftW q) hc0' hc1' (Net.dropW q w) hw'.1 hw'.2 b)
  · push Not at hq
    set x : ℕ → Bool := fun j => (c j).getD false
    have e : ∀ v, mc (N' + 1) .hg [0, 1] (setCtl c w v) =
        mc (N' + 1) .hg [0, 1] (setCtl (colOn 2 (N' + 1) x) w v) := by
      intro v
      apply Net.mc_congr
      intro i hi
      by_cases hiw : i = w
      · simp [setCtl, hiw]
      · rcases i with _ | _ | i
        · simp [setCtl, hiw, hc0, colOn]
        · simp [setCtl, hiw, hc1, colOn]
        · have hci := hq (i + 2) (by omega) hi hiw
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hci
          simp [setCtl, hiw, colOn, hy, x, hi]
    rw [e, e, e]
    exact D.eq310 (N' + 1) hN ih x w hw1 hw2 b

/-- (310) for the multi-controlled `H` on the wires `0, 1`, any controls. -/
theorem mergeHg0 : ∀ (M : ℕ), IH (M + 3) → ∀ (c : ℕ → Option Bool), c 0 = none → c 1 = none →
    ∀ w, 2 ≤ w → w < M + 3 → ∀ b : Bool,
      Derivable (theory (M + 3))
        (drawn [mc (M + 3) .hg [0, 1] (setCtl c w (some b)),
          mc (M + 3) .hg [0, 1] (setCtl c w (some !b))])
        (mc (M + 3) .hg [0, 1] (setCtl c w none)) := by
  intro M
  induction M with
  | zero =>
    intro ih
    exact merge_step_hg0 (N' := 2) (by omega) ih fun c' _ _ w' h1 h2 b => absurd h2 (by omega)
  | succ M ihM =>
    intro ih
    exact merge_step_hg0 (N' := M + 3) (by omega) ih (ihM (ih.mono (by omega)))

/-- The multi-controlled `H` on the wires `0, 1` over every colouring of the
wires `ws`: merged, they are the gate with those wires idle. -/
theorem mergeListH0 {M : ℕ} (ih : IH (M + 3)) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → 0 ∉ ws → 1 ∉ ws →
      (∀ w ∈ ws, w < M + 3) → base 0 = none → base 1 = none →
      Derivable (theory (M + 3))
        (drawn ((List.range (2 ^ ws.length)).map fun i => mc (M + 3) .hg [0, 1] (E.bitsOn ws i base)))
        (mc (M + 3) .hg [0, 1] (E.idleOn ws base))
  | [], base, _, _, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil,
      MergeAll.drawn_one', E.bitsOn, E.idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, h0, h1, hws, hb0, hb1 => by
    have hnd' := List.nodup_cons.1 hnd
    have hw0 : w ≠ 0 := fun e => h0 (by simp [e])
    have hw1 : w ≠ 1 := fun e => h1 (by simp [e])
    have ih' := mergeListH0 ih ws (setCtl base w none) hnd'.2 (fun h => h0 (by simp [h]))
      (fun h => h1 (by simp [h])) (fun x hx => hws x (by simp [hx]))
      (by simp [setCtl, Ne.symm hw0, hb0]) (by simp [setCtl, Ne.symm hw1, hb1])
    refine Derivable.trans ?_ ih'
    rw [List.length_cons, pow_succ, mul_comm, E.range_double, E.drawn_flatMap]
    apply E.drawn_map_congr
    intro i _
    have e0 : E.bitsOn (w :: ws) (2 * i) base = setCtl (E.bitsOn ws i base) w (some false) := by
      simp only [E.bitsOn]; congr 2 <;> simp [Nat.mul_div_cancel_left]
    have e1 : E.bitsOn (w :: ws) (2 * i + 1) base = setCtl (E.bitsOn ws i base) w (some true) := by
      simp only [E.bitsOn]; congr 2 <;> simp [Nat.mul_add_div] <;> omega
    rw [e0, e1, ← E.setCtl_bitsOn ws i base w none hnd'.1]
    have hc0 : E.bitsOn ws i base 0 = none := by
      rw [E.bitsOn_of_not_mem ws i base 0 (fun h => h0 (by simp [h]))]; exact hb0
    have hc1 : E.bitsOn ws i base 1 = none := by
      rw [E.bitsOn_of_not_mem ws i base 1 (fun h => h1 (by simp [h]))]; exact hb1
    exact mergeHg0 M ih (E.bitsOn ws i base) hc0 hc1 w (by omega) (hws w (by simp)) false

/-! ## The frame of the multi-controlled `H` -/

/-- The swaps of the wires `0, 1` and `1, 2` carry the multi-controlled `H`
on the wires `0, 1` to the one with its box on wire `2`, its `H` on wire `0`. -/
theorem hgR {N : ℕ} (hN : 3 ≤ N) (c : ℕ → Option Bool) (h0 : c 0 = none) (h1 : c 1 = none) :
    Derivable (theory N) (swAt N 1 * (swAt N 0 * mc N .hg [0, 1] c * swAt N 0) * swAt N 1)
      (mc N .hg [2, 0] ((c ∘ Net.tau 0) ∘ Net.tau 1)) := by
  have d0 := mc_swap N 0 (by omega) .hg [0, 1] c rfl (by decide)
    (by intro t ht; simp at ht; omega)
    (by intro ⟨h, _⟩; rw [MS.mem_ctrlWires] at h; exact h.2.2 (by simp))
  have e0 : ([0, 1] : List ℕ).map (Net.tau 0) = [1, 0] := rfl
  rw [e0, show drawn [swAt N 0, mc N .hg [0, 1] c, swAt N 0] =
    swAt N 0 * mc N .hg [0, 1] c * swAt N 0 by simp [drawn, mul_assoc]] at d0
  have d1 := mc_swap N 1 (by omega) .hg [1, 0] (c ∘ Net.tau 0) rfl (by decide)
    (by intro t ht; simp at ht; omega)
    (by intro ⟨h, _⟩; rw [MS.mem_ctrlWires] at h; exact h.2.2 (by simp))
  have e1 : ([1, 0] : List ℕ).map (Net.tau 1) = [2, 0] := rfl
  rw [e1, show drawn [swAt N 1, mc N .hg [1, 0] (c ∘ Net.tau 0), swAt N 1] =
    swAt N 1 * mc N .hg [1, 0] (c ∘ Net.tau 0) * swAt N 1 by simp [drawn, mul_assoc]] at d1
  exact (dctx _ _ d0).trans d1

/-- The relabeling as a conjugation. -/
abbrev uR (N : ℕ) : Circ N := swAt N 1 * swAt N 0
abbrev uR' (N : ℕ) : Circ N := swAt N 0 * swAt N 1

theorem uR_inv {N : ℕ} (hN : 3 ≤ N) :
    Derivable (theory N) (uR' N * uR N) 1 ∧ Derivable (theory N) (uR N * uR' N) 1 := by
  have s0 := swsw N 0 (by omega)
  have s1 := swsw N 1 (by omega)
  constructor
  · have e : uR' N * uR N = swAt N 0 * (swAt N 1 * swAt N 1) * swAt N 0 := by
      simp only [uR, uR', mul_assoc]
    rw [e]; refine (dctx _ _ s1).trans ?_; simpa only [mul_one] using s0
  · have e : uR N * uR' N = swAt N 1 * (swAt N 0 * swAt N 0) * swAt N 1 := by
      simp only [uR, uR', mul_assoc]
    rw [e]; refine (dctx _ _ s0).trans ?_; simpa only [mul_one] using s1

theorem uR_conj {N : ℕ} (X : Circ N) :
    uR N * X * uR' N = swAt N 1 * (swAt N 0 * X * swAt N 0) * swAt N 1 := by
  simp only [uR, uR', mul_assoc]

/-! ## `CH` is the multi-controlled `H` with no control but wire `1` -/

/-- On three wires: two swaps and (f4). -/
theorem hg_ch3 : Derivable (theory 3) (mc 3 .hg [2, 0] (ctlAt 1 true)) (ch : Circ 3) := by
  have h := hgR (N := 3) le_rfl (ctlAt 2 true) rfl rfl
  have e : mc 3 .hg [2, 0] ((ctlAt 2 true ∘ Net.tau 0) ∘ Net.tau 1) = mc 3 .hg [2, 0] (ctlAt 1 true) :=
    Net.mc_congr _ _ _ (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl)
  rw [e] at h
  have ec : mc 3 .hg [0, 1] (ctlAt 2 true) = (shift ch : Circ 3) := by
    have e1 : mc 3 .hg [0, 1] (ctlAt 2 true) = mc 3 .hg [0, 1] (blackOn 2 3) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl)
    rw [e1]
    exact Net.mc_canon .hg 1
  rw [ec] at h
  -- (f4): `shift ch, S₀, S₁ = S₀, S₁, ch`
  have f4 : Derivable (theory 3) (drawn [shift ch, swap, shift swap]) (drawn [swap, shift swap, ch]) :=
    derivable_rule Rule.f4 0
  have s0 : swAt 3 0 = (swap : Circ 3) := rfl
  have s1 : swAt 3 1 = (shift swap : Circ 3) := rfl
  rw [s0, s1] at h
  have hs0 := swap_inv 1
  have hs1 : Derivable (theory 3) ((shift swap : Circ 3) * shift swap) 1 := by
    rw [← s1]; exact swsw 3 1 (by omega)
  -- `S₁ (S₀ (shift ch) S₀) S₁ = (S₁ S₀ shift ch) S₀ S₁ = (ch S₁ S₀) S₀ S₁ = ch`
  have f4' : Derivable (theory 3) ((shift swap : Circ 3) * swap * shift ch) (ch * shift swap * swap) := by
    simpa [drawn, mul_assoc] using f4
  have e2 : (shift swap : Circ 3) * (swap * shift ch * swap) * shift swap =
      ((shift swap : Circ 3) * swap * shift ch) * (swap * shift swap) := by simp only [mul_assoc]
  rw [e2] at h
  refine h.symm.trans ((dright _ f4').trans ?_)
  have e3 : (ch : Circ 3) * shift swap * swap * (swap * shift swap) =
      ch * shift swap * (swap * swap) * shift swap := by simp only [mul_assoc]
  rw [e3]
  refine (cancel_mid hs0 _ _).trans ?_
  rw [mul_assoc]
  simpa only [mul_one] using dleft (ch : Circ 3) hs1

/-- At every width from three. -/
theorem hg_ch (M : ℕ) :
    Derivable (theory (M + 3)) (mc (M + 3) .hg [2, 0] (ctlAt 1 true)) (ch : Circ (M + 3)) := by
  have h := der_atBot hg_ch3 (M + 3) (by omega)
  have eA := mc_atBot (k := 3) .hg [2, 0] (ctlAt 1 true) rfl (by decide) (by decide)
    (fun j hj => by simp [ctlAt]; omega) (M + 3) (by omega)
  have eC : atBot (M + 3) (ch : Circ 3) = (ch : Circ (M + 3)) :=
    atBot_loc (K := 3) (.s (.K 0)) rfl (M + 3) (by omega)
  rw [← eA, eC] at h
  exact h

/-! ## The colourings of the wires `3, …` -/

/-- The wires `3, …, M + 2`. -/
abbrev S3 (M : ℕ) : List ℕ := (List.range M).map (· + 3)

theorem S3_nodup (M : ℕ) : (S3 M).Nodup :=
  List.Nodup.map (fun a b h => by simpa using h) List.nodup_range

theorem mem_S3 {M j : ℕ} : j ∈ S3 M ↔ 3 ≤ j ∧ j < M + 3 := by
  simp only [S3, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨j - 3, by omega, by omega⟩

/-- The colours of the `i`-th colouring of the wires `3, …`. -/
def colS (M i : ℕ) : ℕ → Bool := fun j => (E.bitsOn (S3 M) i (ctlAt 2 true) j).getD false

/-- The frame gate of the `i`-th colouring, wire `2` black. -/
theorem bitsOnS (M i : ℕ) : ∀ j < M + 3, E.bitsOn (S3 M) i (ctlAt 2 true) j =
    ctlOr (ctlAt 2 true) (colOn 3 (M + 3) (colS M i)) j := by
  intro j hj
  by_cases hjS : j ∈ S3 M
  · obtain ⟨b, hb⟩ := MergeAll.bitsOn_mem (S3 M) i (ctlAt 2 true) j hjS
    have h2 := mem_S3.1 hjS
    simp [colS, hb, colOn, ctlOr, ctlAt, show j ≠ 2 by omega, show 3 ≤ j by omega, hj]
  · rw [MergeAll.bitsOn_apply_not_mem hjS]
    have : j < 3 := by rw [mem_S3] at hjS; omega
    simp [colOn, ctlOr, ctlAt, show ¬ 3 ≤ j by omega]

theorem colS_white {M i : ℕ} (hi : i + 1 < 2 ^ M) :
    ∃ j, 3 ≤ j ∧ j < M + 3 ∧ colS M i j = false := by
  obtain ⟨j, hj, hb⟩ := MergeAll.bitsOn_white (S3 M) i (ctlAt 2 true) (S3_nodup M) (by simpa using hi)
  exact ⟨j, (mem_S3.1 hj).1, (mem_S3.1 hj).2, by simp [colS, hb]⟩

theorem colS_last {M : ℕ} : ∀ j, 3 ≤ j → j < M + 3 → colS M (2 ^ M - 1) j = true := by
  intro j h3 hj
  have hjS : j ∈ S3 M := mem_S3.2 ⟨h3, hj⟩
  have := MergeAll.bitsOn_last (S3 M) (ctlAt 2 true) j hjS
  have hlen : (S3 M).length = M := by simp
  rw [hlen] at this
  simp [colS, this]

/-- The multi-controlled `H` of (333) for the colouring `x` of the wires `3, …`. -/
abbrev HGc (M : ℕ) (x : ℕ → Bool) : Circ (M + 3) :=
  mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (colOn 3 (M + 3) x))

/-- Its frame version, on the wires `0, 1`. -/
abbrev HFc (M : ℕ) (x : ℕ → Bool) : Circ (M + 3) :=
  mc (M + 3) .hg [0, 1] (ctlOr (ctlAt 2 true) (colOn 3 (M + 3) x))

theorem HFc_R (M : ℕ) (x : ℕ → Bool) :
    Derivable (theory (M + 3)) (uR (M + 3) * HFc M x * uR' (M + 3)) (HGc M x) := by
  rw [uR_conj]
  refine (hgR (by omega) _ (by simp [ctlOr, ctlAt, colOn]) (by simp [ctlOr, ctlAt, colOn])).trans
    (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | rfl | h3
  · simp [ctlOr, ctlAt, colOn, Net.tau]
  · simp [ctlOr, ctlAt, colOn, Net.tau]
  · simp [ctlOr, ctlAt, colOn, Net.tau]
  · simp [Function.comp, Net.tau_of_gt (show 0 + 1 < i by omega),
      Net.tau_of_gt (show 1 + 1 < i by omega), ctlOr, ctlAt, show i ≠ 2 by omega,
      show i ≠ 1 by omega]

/-- The frame version on the colouring `colOn 2`. -/
theorem HFc_col2 (M : ℕ) (x : ℕ → Bool) :
    HFc M x = mc (M + 3) .hg [0, 1] (colOn 2 (M + 3) (fun j => if j = 2 then true else x j)) :=
  Net.mc_congr _ _ _ (fun i hi => by
    rcases (by omega : i < 2 ∨ i = 2 ∨ 3 ≤ i) with h | rfl | h
    · simp [ctlOr, ctlAt, colOn, show i ≠ 2 by omega, show ¬ 3 ≤ i by omega,
        show ¬ 2 ≤ i by omega]
    · simp [ctlOr, ctlAt, colOn, hi]
    · simp [ctlOr, ctlAt, colOn, show i ≠ 2 by omega, h, hi, show 2 ≤ i by omega])

/-! ## The multi-controlled `H` gates commute and are involutions -/

theorem hg340 (M : ℕ) (ih : IH (M + 3)) (x y : ℕ → Bool) :
    Comm (M + 3) (mc (M + 3) .hg [0, 1] (colOn 2 (M + 3) x))
      (mc (M + 3) .hg [0, 1] (colOn 2 (M + 3) y)) := by
  rcases M with _ | _ | M
  · exact comm340_3 ih x y
  · exact comm340_4 ih x y
  · exact comm340_ge5 (M + 2 + 3) (by omega) ih x y

theorem HGc_comm (M : ℕ) (ih : IH (M + 3)) (x y : ℕ → Bool) :
    Comm (M + 3) (HGc M x) (HGc M y) := by
  have h := hg340 M ih (fun j => if j = 2 then true else x j) (fun j => if j = 2 then true else y j)
  rw [← HFc_col2 M x, ← HFc_col2 M y] at h
  exact Comm.congr (HFc_R M x) (HFc_R M y) (Comm.conj h (uR_inv (by omega)).1)

theorem HGc_inv (M : ℕ) (ih : IH (M + 3)) (x : ℕ → Bool) :
    Derivable (theory (M + 3)) (HGc M x * HGc M x) 1 := by
  have h := D.eq312 (M + 3) (by omega) ih (fun j => if j = 2 then true else x j)
  rw [drawn_two, ← HFc_col2 M x] at h
  have hu := uR_inv (N := M + 3) (by omega)
  have k := conj_inv2 hu.1 hu.2 h
  exact ((dmul (HFc_R M x) (HFc_R M x)).symm.trans k)

/-! ## The merge -/

/-- `CH` is the product of the multi-controlled `H` over every colouring of
the wires `3, …`. -/
theorem merged (M : ℕ) (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (ch : Circ (M + 3))
      (drawn ((List.range (2 ^ M)).map fun i => HGc M (colS M i))) := by
  have hm := mergeListH0 ih (S3 M) (ctlAt 2 true) (S3_nodup M) (by rw [mem_S3]; omega)
    (by rw [mem_S3]; omega) (fun w hw => (mem_S3.1 hw).2) rfl rfl
  have hlen : (S3 M).length = M := by simp
  rw [hlen] at hm
  have eI : mc (M + 3) .hg [0, 1] (E.idleOn (S3 M) (ctlAt 2 true)) = mc (M + 3) .hg [0, 1] (ctlAt 2 true) :=
    Net.mc_congr _ _ _ (fun j hj => by
      rw [MergeAll.idleOn_apply]
      by_cases hjS : j ∈ S3 M
      · rw [if_pos hjS]; have := mem_S3.1 hjS; simp [ctlAt]; omega
      · rw [if_neg hjS])
  have eF : ∀ i, mc (M + 3) .hg [0, 1] (E.bitsOn (S3 M) i (ctlAt 2 true)) = HFc M (colS M i) :=
    fun i => Net.mc_congr _ _ _ (bitsOnS M i)
  simp only [eF] at hm
  rw [eI] at hm
  have hu := uR_inv (N := M + 3) (by omega)
  -- conjugate the merge into the frame of `hg[2, 0]`
  have k := (dright _ (dleft _ hm.symm)).trans (conj_drawn hu.1 hu.2 _)
  have eR : Derivable (theory (M + 3)) (uR (M + 3) * mc (M + 3) .hg [0, 1] (ctlAt 2 true) * uR' (M + 3))
      (mc (M + 3) .hg [2, 0] (ctlAt 1 true)) := by
    rw [uR_conj]
    refine (hgR (by omega) _ rfl rfl).trans (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | rfl | h3
    · rfl
    · rfl
    · rfl
    · simp [Function.comp, Net.tau_of_gt (show 0 + 1 < i by omega),
        Net.tau_of_gt (show 1 + 1 < i by omega), ctlAt, show i ≠ 2 by omega, show i ≠ 1 by omega]
  refine (hg_ch M).symm.trans (eR.symm.trans (k.trans ?_))
  rw [List.map_map]
  exact E.drawn_map_congr _ (fun i _ => HFc_R M (colS M i))

/-! ## (339) in the frame of (333) -/

theorem box_last (M : ℕ) : mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) =
    mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 true) (colOn 3 (M + 3) (fun _ => true)))) :=
  Net.mc_congr _ _ _ (by ctl_case33)

/-- (339) relabeled: the multi-controlled `H` of a colouring other than the
black one passes the box on wire `1`. -/
theorem HGc_B (M : ℕ) (ih : IH (M + 3))
    (h339 : ∀ y : ℕ → Bool, DiffOn 3 (M + 3) (fun _ => true) y →
      Comm (M + 3) (mc (M + 3) .box [0] (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true)
        (colOn 3 (M + 3) (fun _ => true)))))
        (mc (M + 3) .hg [1, 2] (ctlOr (ctlAt 0 true) (colOn 3 (M + 3) y))))
    (y : ℕ → Bool) (hy : DiffOn 3 (M + 3) (fun _ => true) y) :
    Comm (M + 3) (HGc M y) (mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))) := by
  have h := h339 y hy
  -- the swap of the wires `1, 2`
  have a1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true) (colOn 3 (M + 3) (fun _ => true))))
    (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (colOn 3 (M + 3) (fun _ => true)))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case33)
  have b1 := swBH ih 1 (by omega) .hg (Or.inr rfl) [1, 2] [2, 1]
    (ctlOr (ctlAt 0 true) (colOn 3 (M + 3) y))
    (ctlOr (ctlAt 0 true) (colOn 3 (M + 3) y)) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case33)
  have k1 := Comm.congr a1 b1 (Comm.conj h (swsw (M + 3) 1 (by omega)))
  -- the swap of the wires `0, 1`
  have a0 := swBH ih 0 (by omega) .box (Or.inl rfl) [0] [1]
    (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (colOn 3 (M + 3) (fun _ => true))))
    (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 true) (colOn 3 (M + 3) (fun _ => true)))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case33)
  have b0 := swBH ih 0 (by omega) .hg (Or.inr rfl) [2, 1] [2, 0]
    (ctlOr (ctlAt 0 true) (colOn 3 (M + 3) y))
    (ctlOr (ctlAt 1 true) (colOn 3 (M + 3) y)) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case33)
  have k0 := Comm.congr a0 b0 (Comm.conj k1 (swsw (M + 3) 0 (by omega)))
  rw [box_last]
  exact Derivable.symm k0

/-! ## (333) and (334) -/

theorem alg333 {N : ℕ} {a b p : Circ N} (hpb : Comm N p b) (hpa : Comm N p a)
    (hpp : Derivable (theory N) (p * p) 1) :
    Derivable (theory N) (b * (a * p) * b * (a * p)) (b * a * b * a) := by
  unfold Comm at hpb hpa
  rw [drawn_two, drawn_two] at hpb hpa
  -- hpb : b * p ≈ p * b, hpa : a * p ≈ p * a
  have e1 : b * (a * p) * b * (a * p) = b * a * (p * b) * (a * p) := by simp only [mul_assoc]
  rw [e1]
  refine (dright _ (dleft _ hpb.symm)).trans ?_
  have e2 : b * a * (b * p) * (a * p) = b * a * b * (p * a) * p := by simp only [mul_assoc]
  rw [e2]
  refine (dright _ (dleft _ hpa.symm)).trans ?_
  have e3 : b * a * b * (a * p) * p = b * a * b * a * (p * p) := by simp only [mul_assoc]
  rw [e3]
  simpa only [mul_one] using dleft (b * a * b * a) hpp

/-- The box of (333), on wire `1`. -/
abbrev B333 (M : ℕ) : Circ (M + 3) := mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))

/-- The multi-controlled `H` of (333). -/
abbrev HG333 (M : ℕ) : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3)))

theorem HGc_black (M : ℕ) : HGc M (fun _ => true) = HG333 M :=
  Net.mc_congr _ _ _ (by ctl_case33)

theorem HGc_last (M : ℕ) : HGc M (colS M (2 ^ M - 1)) = HG333 M :=
  Net.mc_congr _ _ _ (fun i hi => by
    by_cases h3 : 3 ≤ i
    · simp [ctlOr, ctlAt, colOn, blackOn, colS_last i h3 hi, h3, hi, show i ≠ 1 by omega]
    · simp [ctlOr, ctlAt, colOn, blackOn, h3])

/-- The box of Definition 2.4's `ZX`, conjugated by the swap of the wires
`0, 1`, is the box on wire `1`. -/
theorem box1_s0 (M : ℕ) : Derivable (theory (M + 3)) (conj swap (box (M + 2))) (B333 M) := by
  have eS : swAt (M + 3) 0 = (swap : Circ (M + 3)) := rfl
  have eBx : box (M + 2) = mc (M + 3) .box [0] (blackOn 1 (M + 3)) := (Net.mc_canon .box (M + 2)).symm
  rw [eBx, conj, ← eS, show drawn [swAt (M + 3) 0, mc (M + 3) .box [0] (blackOn 1 (M + 3)),
    swAt (M + 3) 0] = swAt (M + 3) 0 * mc (M + 3) .box [0] (blackOn 1 (M + 3)) * swAt (M + 3) 0 by
    simp [drawn, mul_assoc]]
  exact mc_s0 (M + 3) (by omega) .box 0 (by omega) _ _ (by decide) (by ctl_case33)

/-- (333), given (339) at the same width. -/
theorem comm333 (M : ℕ) (ih : IH (M + 3))
    (h339 : ∀ y : ℕ → Bool, DiffOn 3 (M + 3) (fun _ => true) y →
      Comm (M + 3) (mc (M + 3) .box [0] (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true)
        (colOn 3 (M + 3) (fun _ => true)))))
        (mc (M + 3) .hg [1, 2] (ctlOr (ctlAt 0 true) (colOn 3 (M + 3) y)))) :
    Derivable (theory (M + 3)) (mc (M + 3) .zx [0] (blackOn 1 (M + 3)))
      (drawn [mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))),
        mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))),
        mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))),
        mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))]) := by
  -- Definition 2.4
  have eZ : mc (M + 3) .zx [0] (blackOn 1 (M + 3)) =
      drawn [(ch : Circ (M + 3)), conj swap (box (M + 2)), ch, conj swap (box (M + 2))] :=
    Net.mc_canon .zx (M + 2)
  -- the merge of `CH`, the black factor last
  have hL : 2 ^ M = (2 ^ M - 1) + 1 := by have := Nat.one_le_two_pow (n := M); omega
  have hm := merged M ih
  rw [hL, List.range_succ, List.map_append, SE.drawn_append] at hm
  simp only [List.map_cons, List.map_nil, MergeAll.drawn_one'] at hm
  rw [HGc_last] at hm
  -- the product `P` of the other colourings
  have cpB : Comm (M + 3) (drawn ((List.range (2 ^ M - 1)).map fun i => HGc M (colS M i)))
      (B333 M) := comm_drawn_left _ (fun g hg => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    have hi' : i < 2 ^ M - 1 := by simpa using hi
    obtain ⟨j, hj3, hjN, hxj⟩ := colS_white (M := M) (i := i) (by omega)
    exact HGc_B M ih h339 _ ⟨j, hj3, hjN, by simp [hxj]⟩)
  have cpH : Comm (M + 3) (drawn ((List.range (2 ^ M - 1)).map fun i => HGc M (colS M i)))
      (HG333 M) := comm_drawn_left _ (fun g hg => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hg
    rw [← HGc_black]
    exact HGc_comm M ih (colS M i) (fun _ => true))
  have pp : Derivable (theory (M + 3))
      (drawn ((List.range (2 ^ M - 1)).map fun i => HGc M (colS M i)) *
        drawn ((List.range (2 ^ M - 1)).map fun i => HGc M (colS M i))) 1 :=
    MergeAll.prod_cancel (fun i => HGc M (colS M i)) (fun i => HGc M (colS M i)) (2 ^ M - 1)
      (fun i _ j _ _ => HGc_comm M ih _ _) (fun i _ => HGc_inv M ih _)
  -- assemble
  have hBs := box1_s0 M
  have e6 : drawn [(ch : Circ (M + 3)), conj swap (box (M + 2)), ch, conj swap (box (M + 2))] =
      conj swap (box (M + 2)) * ch * conj swap (box (M + 2)) * ch := by
    simp [drawn, mul_assoc]
  have e5 : drawn [HG333 M, B333 M, HG333 M, B333 M] = B333 M * HG333 M * B333 M * HG333 M := by
    simp [drawn, mul_assoc]
  show Derivable (theory (M + 3)) (mc (M + 3) .zx [0] (blackOn 1 (M + 3)))
    (drawn [HG333 M, B333 M, HG333 M, B333 M])
  rw [eZ, e6, e5]
  exact (dmul (dmul (dmul hBs hm) hBs) hm).trans (alg333 cpB cpH pp)

theorem B333_inv (M : ℕ) (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (B333 M * B333 M) 1 := by
  have h := D.eq311 (M + 3) (by omega) ih (fun _ => true)
  have e : mc (M + 3) .box [0] (colOn 1 (M + 3) (fun _ => true)) = box (M + 2) :=
    (Net.mc_congr _ _ _ (fun i hi => by
      simp only [colOn, blackOn, Net.kindSp]; split_ifs <;> first | rfl | omega)).trans
      (Net.mc_canon .box (M + 2))
  rw [drawn_two, e] at h
  have hs := swap_inv (M + 1)
  have k := conj_inv2 hs hs h
  have hB := box1_s0 M
  have e2 : conj swap (box (M + 2)) = (swap : Circ (M + 3)) * box (M + 2) * swap := by
    simp [conj, drawn, mul_assoc]
  rw [e2] at hB
  exact (dmul hB hB).symm.trans k

theorem HG333_inv (M : ℕ) (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (HG333 M * HG333 M) 1 := by
  rw [← HGc_black]; exact HGc_inv M ih _

/-- (334), from (333) and (317): the multi-controlled `XZ` is the inverse of
the `ZX`, and the inverse of `B HG B HG` is `HG B HG B` (Lemma B.5). -/
theorem comm334 (M : ℕ) (ih : IH (M + 3))
    (h333 : Derivable (theory (M + 3)) (mc (M + 3) .zx [0] (blackOn 1 (M + 3)))
      (drawn [HG333 M, B333 M, HG333 M, B333 M]))
    (h317 : Derivable (theory (M + 3))
      (drawn [mc (M + 3) .zx [0] (blackOn 1 (M + 3)), mc (M + 3) .xz [0] (blackOn 1 (M + 3))]) 1) :
    Derivable (theory (M + 3)) (mc (M + 3) .xz [0] (blackOn 1 (M + 3)))
      (drawn [mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))),
        mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3))),
        mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))),
        mc (M + 3) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (M + 3)))]) := by
  show Derivable (theory (M + 3)) (mc (M + 3) .xz [0] (blackOn 1 (M + 3)))
    (drawn [B333 M, HG333 M, B333 M, HG333 M])
  set Z := mc (M + 3) .zx [0] (blackOn 1 (M + 3))
  set X := mc (M + 3) .xz [0] (blackOn 1 (M + 3))
  have eW : drawn [HG333 M, B333 M, HG333 M, B333 M] = B333 M * HG333 M * B333 M * HG333 M := by
    simp [drawn, mul_assoc]
  have eW' : drawn [B333 M, HG333 M, B333 M, HG333 M] = HG333 M * B333 M * HG333 M * B333 M := by
    simp [drawn, mul_assoc]
  rw [eW] at h333
  rw [eW']
  rw [drawn_two] at h317
  have hWW := palin (B333_inv M ih) (HG333_inv M ih)
  -- `X = X (W W') = (X W) W' = (X Z) W' = W'`
  have s1 : Derivable (theory (M + 3)) X (X * ((B333 M * HG333 M * B333 M * HG333 M) *
      (HG333 M * B333 M * HG333 M * B333 M))) := by
    simpa only [mul_one] using (dleft X hWW).symm
  refine s1.trans ?_
  rw [← mul_assoc]
  refine (dright _ (dleft X h333.symm)).trans ?_
  simpa only [one_mul] using dright (HG333 M * B333 M * HG333 M * B333 M) h317

end QCert.RealCliffordCH.Sec8.D.N13
