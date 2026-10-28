/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: merging multi-controlled gates over all colourings

Equation (309) merges a black and a white control of the box on one wire,
the other wires all being controls.  The proof of Lemma 8.6 merges the
boxes over every colouring of several wires, so the boxes met after the
first merge have idle wires.  An idle wire moved to the top (`Net.mc_toTop`)
leaves an equation one wire down (`top_lift`), so (309) with idle wires is
(309) on fewer wires (`mergeC`, by induction on the width; on two wires it
is decided).  Moved to any box wire by a frame (`mergeAt`), and iterated
over the colourings of a list of wires (`mergeList`), it gives the products
of the proof of Lemma 8.6.
-/
import QCert.RealCliffordCH.Sec8.E.Transport
import QCert.RealCliffordCH.Sec8.E.Lemma84
import QCert.RealCliffordCH.Sec8.Fast

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-- (309) for the box on wire `t`, any controls. -/
theorem mergeAt {M : ℕ} (ih : IH (M + 3)) {t : ℕ} (ht : t < M + 3) (c : ℕ → Option Bool)
    (hc : c t = none) {w : ℕ} (hwt : w ≠ t) (hw : w < M + 3) (b : Bool) :
    Derivable (theory (M + 3))
      (drawn [mc (M + 3) .box [t] (setCtl c w (some b)), mc (M + 3) .box [t] (setCtl c w (some !b))])
      (mc (M + 3) .box [t] (setCtl c w none)) := by
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have hπ0 : frm [t] 0 = t := frm_getD hnd hps (by simp)
  set w' := pos (netOf [t]) w
  have hw' : w' < M + 3 := pos_lt _ (netOf_ok hnd hps) w hw
  have hw'0 : w' ≠ 0 := by
    intro h; apply hwt; rw [← frm_pos [t] w, show pos (netOf [t]) w = 0 from h, hπ0]
  have hsw := mcSwapAll ih
  have fr : ∀ v, Derivable (theory (M + 3))
      (placedBy (M + 3) (netOf [t]) (mc (M + 3) .box [0] (setCtl (c ∘ frm [t]) w' v)))
      (mc (M + 3) .box [t] (setCtl c w v)) := by
    intro v
    have := frame hsw hnd hps .box [0] (setCtl c w v) rfl (by simp) (by simp)
    rw [setCtl_frm] at this
    simpa [hπ0] using this
  have hc' : (c ∘ frm [t]) 0 = none := by simp [hπ0, hc]
  have := via_frame (L := [mc (M + 3) .box [t] (setCtl c w (some b)),
      mc (M + 3) .box [t] (setCtl c w (some !b))]) (R := [mc (M + 3) .box [t] (setCtl c w none)])
    hnd hps (List.Forall₂.cons (fr _) (List.Forall₂.cons (fr _) List.Forall₂.nil))
    (List.Forall₂.cons (fr _) List.Forall₂.nil) (by
      rw [drawn_single]; exact mergeC M ih _ hc' w' (by omega) hw' b)
  rwa [drawn_single] at this

/-! ## Merging over every colouring of a list of wires -/

/-- The boxes on wire `t` over every colouring of the wires `ws`, the other
controls fixed, merge into the box with the wires `ws` idle. -/
theorem mergeList {M : ℕ} (ih : IH (M + 3)) {t : ℕ} (ht : t < M + 3) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → t ∉ ws → (∀ w ∈ ws, w < M + 3) →
      base t = none →
      Derivable (theory (M + 3))
        (drawn ((List.range (2 ^ ws.length)).map fun i => mc (M + 3) .box [t] (bitsOn ws i base)))
        (mc (M + 3) .box [t] (idleOn ws base))
  | [], base, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil, drawn_single,
      bitsOn, idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, htw, hws, hb => by
    have hnd' := List.nodup_cons.1 hnd
    have hwt : w ≠ t := fun e => htw (by simp [e])
    have ih' := mergeList ih ht ws (setCtl base w none) hnd'.2 (fun h => htw (by simp [h]))
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
    have hct : bitsOn ws i base t = none := by
      rw [bitsOn_of_not_mem ws i base t (fun h => htw (by simp [h]))]; exact hb
    exact mergeAt ih ht (bitsOn ws i base) hct hwt (hws w (by simp)) false

end QCert.RealCliffordCH.Sec8.E
