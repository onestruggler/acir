/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: merging multi-controlled `H` gates over all colourings

Equation (310) with idle wires (`mergeHgC`, by induction on the width as
`mergeC`: an idle wire is moved to the top), at any wires (`mergeHgAt`, by a
frame), and over every colouring of a list of wires (`mergeListGen`, for any
kind of gate given its merge step).
-/
import QCert.RealCliffordCH.Sec8.E.Lemma87

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

theorem merge_step_hg {N' : ℕ} (hN : 3 ≤ N' + 1) (ih : IH (N' + 1))
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
        (mc N' .hg [0, 1] (setCtl (c ∘ liftW q) (dropW q w) v)) := by
      intro v
      have := ToTop.mc (M := N') (q := q) (by omega) .hg [0, 1] (setCtl c w v) rfl (by simp)
        (by simp; omega) (by simp; omega) (by simp [setCtl, hqw, hcq])
      have e0 : [0, 1].map (dropW q) = [0, 1] := by
        simp [dropW, show 0 < q by omega, show 1 < q by omega]
      rwa [setCtl_liftW (Ne.symm hqw), e0] at this
    have hc0' : (c ∘ liftW q) 0 = none := by simp [liftW, show 0 < q by omega, hc0]
    have hc1' : (c ∘ liftW q) 1 = none := by simp [liftW, show 1 < q by omega, hc1]
    have hw' : 2 ≤ dropW q w ∧ dropW q w < N' := by simp only [dropW]; split_ifs <;> omega
    exact liftIdle (ToTop.ofList (List.Forall₂.cons (hA _) (List.Forall₂.cons (hA _)
      List.Forall₂.nil))) (hA none) (down (c ∘ liftW q) hc0' hc1' (dropW q w) hw'.1 hw'.2 b)
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

/-- (310) for the multi-controlled `H` on the wires `0`, `1`, any controls. -/
theorem mergeHgC : ∀ (M : ℕ), IH (M + 3) → ∀ (c : ℕ → Option Bool), c 0 = none → c 1 = none →
    ∀ w, 2 ≤ w → w < M + 3 → ∀ b : Bool,
      Derivable (theory (M + 3))
        (drawn [mc (M + 3) .hg [0, 1] (setCtl c w (some b)),
          mc (M + 3) .hg [0, 1] (setCtl c w (some !b))])
        (mc (M + 3) .hg [0, 1] (setCtl c w none)) := by
  intro M
  induction M with
  | zero =>
    intro ih
    exact merge_step_hg (N' := 2) (by omega) ih fun c' _ _ w' h1 h2 b => absurd h2 (by omega)
  | succ M ihM =>
    intro ih
    exact merge_step_hg (N' := M + 3) (by omega) ih (ihM (ih.mono (by omega)))

/-- (310) for the multi-controlled `H` with its box on wire `bw` and `H` on wire
`hw`, any controls. -/
theorem mergeHgAt {M : ℕ} (ih : IH (M + 3)) {bw hw : ℕ} (hb : bw < M + 3) (hh : hw < M + 3)
    (hbh : bw ≠ hw) (c : ℕ → Option Bool) (hcb : c bw = none) (hch : c hw = none) {w : ℕ}
    (hwb : w ≠ bw) (hwh : w ≠ hw) (hwN : w < M + 3) (b : Bool) :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) .hg [bw, hw] (setCtl c w (some b)),
        mc (M + 3) .hg [bw, hw] (setCtl c w (some !b))])
      (mc (M + 3) .hg [bw, hw] (setCtl c w none)) := by
  have hnd : [bw, hw].Nodup := by simp [hbh]
  have hps : ∀ p ∈ [bw, hw], p < M + 3 := by simp [hb, hh]
  have hπ0 : frm [bw, hw] 0 = bw := frm_getD hnd hps (by simp)
  have hπ1 : frm [bw, hw] 1 = hw := frm_getD hnd hps (by simp)
  set w' := pos (netOf [bw, hw]) w
  have hw' : w' < M + 3 := pos_lt _ (netOf_ok hnd hps) w hwN
  have hw'2 : 2 ≤ w' := by
    by_contra hlt
    have : w' = 0 ∨ w' = 1 := by omega
    rcases this with h | h
    · apply hwb; rw [← frm_pos [bw, hw] w, show pos (netOf [bw, hw]) w = 0 from h, hπ0]
    · apply hwh; rw [← frm_pos [bw, hw] w, show pos (netOf [bw, hw]) w = 1 from h, hπ1]
  have hsw := mcSwapAll ih
  have fr : ∀ v, Derivable (theory (M + 3))
      (placedBy (M + 3) (netOf [bw, hw]) (mc (M + 3) .hg [0, 1] (setCtl (c ∘ frm [bw, hw]) w' v)))
      (mc (M + 3) .hg [bw, hw] (setCtl c w v)) := by
    intro v
    have := frame hsw hnd hps .hg [0, 1] (setCtl c w v) rfl (by simp) (by simp)
    rw [setCtl_frm] at this
    simpa [hπ0, hπ1] using this
  have hc0 : (c ∘ frm [bw, hw]) 0 = none := by simp [hπ0, hcb]
  have hc1 : (c ∘ frm [bw, hw]) 1 = none := by simp [hπ1, hch]
  have := via_frame (L := [mc (M + 3) .hg [bw, hw] (setCtl c w (some b)),
      mc (M + 3) .hg [bw, hw] (setCtl c w (some !b))]) (R := [mc (M + 3) .hg [bw, hw] (setCtl c w none)])
    hnd hps (List.Forall₂.cons (fr _) (List.Forall₂.cons (fr _) List.Forall₂.nil))
    (List.Forall₂.cons (fr _) List.Forall₂.nil) (by
      rw [drawn_single]; exact mergeHgC M ih _ hc0 hc1 w' hw'2 hw' b)
  rwa [drawn_single] at this

/-- Gates of kind `K` on the special wires `tg` over every colouring of the
wires `ws`, as a product in the order of the colourings, merge into the gate
with the wires `ws` idle, given the merge step for the gate. -/
theorem mergeListGen {N : ℕ} (K : Kind) (tg : List ℕ)
    (hmerge : ∀ c : ℕ → Option Bool, (∀ t ∈ tg, c t = none) → ∀ w, w ∉ tg → w < N → ∀ b : Bool,
      Derivable (theory N) (drawn [mc N K tg (setCtl c w (some b)), mc N K tg (setCtl c w (some !b))])
        (mc N K tg (setCtl c w none))) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → (∀ t ∈ tg, t ∉ ws) →
      (∀ w ∈ ws, w < N) → (∀ t ∈ tg, base t = none) →
      Derivable (theory N)
        ((List.range (2 ^ ws.length)).map fun i => mc N K tg (bitsOn ws i base)).prod
        (mc N K tg (idleOn ws base))
  | [], base, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, bitsOn, idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, htw, hws, hb => by
    have hnd' := List.nodup_cons.1 hnd
    have hwt : w ∉ tg := fun h => htw w h (by simp)
    have ih' := mergeListGen K tg hmerge ws (setCtl base w none) hnd'.2
      (fun t ht h => htw t ht (by simp [h])) (fun x hx => hws x (by simp [hx]))
      (fun t ht => by simp [setCtl, show t ≠ w from fun e => hwt (e ▸ ht), hb t ht])
    refine Derivable.trans ?_ ih'
    rw [List.length_cons, pow_succ, mul_comm]
    apply prod_pairs
    intro i _
    have e0 : bitsOn (w :: ws) (2 * i) base = setCtl (bitsOn ws i base) w (some false) := by
      simp only [bitsOn]; congr 2 <;> simp
    have e1 : bitsOn (w :: ws) (2 * i + 1) base = setCtl (bitsOn ws i base) w (some true) := by
      simp only [bitsOn]; congr 2 <;> simp [Nat.mul_add_div]
    rw [e0, e1, ← setCtl_bitsOn ws i base w none hnd'.1]
    have hct : ∀ t ∈ tg, bitsOn ws i base t = none := by
      intro t ht
      rw [bitsOn_of_not_mem ws i base t (fun h => htw t ht (by simp [h]))]; exact hb t ht
    have := hmerge (bitsOn ws i base) hct w hwt (hws w (by simp)) true
    rwa [drawn_two] at this

end QCert.RealCliffordCH.Sec8.E
