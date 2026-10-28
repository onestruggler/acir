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

/-! ## (309) with idle wires -/

theorem setCtl_liftW {c : ℕ → Option Bool} {w q : ℕ} (hwq : w ≠ q) (v : Option Bool) :
    setCtl c w v ∘ liftW q = setCtl (c ∘ liftW q) (dropW q w) v := by
  funext j
  simp only [Function.comp, setCtl, liftW, dropW]
  split_ifs <;> first | rfl | omega

/-- (309) on two wires: the box on wire `0` controlled by wire `1` in both
colours is the box with no control. -/
theorem merge2 (ih2 : CompleteAt 2) (c : ℕ → Option Bool) (hc : c 0 = none) (b : Bool) :
    Derivable (theory 2) (drawn [mc 2 .box [0] (setCtl c 1 (some b)), mc 2 .box [0] (setCtl c 1 (some !b))])
      (mc 2 .box [0] (setCtl c 1 none)) := by
  have e : ∀ v, mc 2 .box [0] (setCtl c 1 v) = mc 2 .box [0] (fun j => if j = 1 then v else none) := by
    intro v
    apply Net.mc_congr
    intro i hi
    rcases i with _ | _ | i
    · simp [setCtl, hc]
    · simp [setCtl]
    · omega
  rw [e, e, e]
  cases b
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))

/-- One step of the induction: (309) with idle wires on `N' + 1` wires, given it
on `N'` wires.  With an idle wire other than the merged one, it is moved to
the top; otherwise every wire is a control and this is (309). -/
theorem merge_step {N' : ℕ} (hN : 3 ≤ N' + 1) (ih : IH (N' + 1))
    (down : ∀ c' : ℕ → Option Bool, c' 0 = none → ∀ w', 1 ≤ w' → w' < N' → ∀ b : Bool,
      Derivable (theory N')
        (drawn [mc N' .box [0] (setCtl c' w' (some b)), mc N' .box [0] (setCtl c' w' (some !b))])
        (mc N' .box [0] (setCtl c' w' none)))
    (c : ℕ → Option Bool) (hc : c 0 = none) (w : ℕ) (hw1 : 1 ≤ w) (hw2 : w < N' + 1) (b : Bool) :
    Derivable (theory (N' + 1))
      (drawn [mc (N' + 1) .box [0] (setCtl c w (some b)),
        mc (N' + 1) .box [0] (setCtl c w (some !b))])
      (mc (N' + 1) .box [0] (setCtl c w none)) := by
  by_cases hq : ∃ q, 1 ≤ q ∧ q < N' + 1 ∧ q ≠ w ∧ c q = none
  · obtain ⟨q, hq1, hq2, hqw, hcq⟩ := hq
    have hA : ∀ v, ToTop N' q (mc (N' + 1) .box [0] (setCtl c w v))
        (mc N' .box [0] (setCtl (c ∘ liftW q) (dropW q w) v)) := by
      intro v
      have := ToTop.mc (M := N') (q := q) (by omega) .box [0] (setCtl c w v) rfl (by simp)
        (by simp) (by simp; omega) (by simp [setCtl, hqw, hcq])
      have e0 : [0].map (dropW q) = [0] := by simp [dropW]
      rwa [setCtl_liftW (Ne.symm hqw), e0] at this
    have hc' : (c ∘ liftW q) 0 = none := by simp [liftW, show 0 < q by omega, hc]
    have hw' : 1 ≤ dropW q w ∧ dropW q w < N' := by simp only [dropW]; split_ifs <;> omega
    exact liftIdle (ToTop.ofList (List.Forall₂.cons (hA _) (List.Forall₂.cons (hA _)
      List.Forall₂.nil))) (hA none) (down (c ∘ liftW q) hc' (dropW q w) hw'.1 hw'.2 b)
  · push Not at hq
    set x : ℕ → Bool := fun j => (c j).getD false
    have e : ∀ v, mc (N' + 1) .box [0] (setCtl c w v) =
        mc (N' + 1) .box [0] (setCtl (colOn 1 (N' + 1) x) w v) := by
      intro v
      apply Net.mc_congr
      intro i hi
      by_cases hiw : i = w
      · simp [setCtl, hiw]
      · by_cases hi0 : i = 0
        · subst hi0; simp [setCtl, hiw, hc, colOn]
        · have hci := hq i (by omega) hi hiw
          obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hci
          simp [setCtl, hiw, colOn, hy, x, show 1 ≤ i by omega, hi]
    rw [e, e, e]
    exact D.eq309 (N' + 1) hN ih x w hw1 hw2 b

/-- (309) at the box wire `0` for any controls (some wires may be idle). -/
theorem mergeC : ∀ (M : ℕ), IH (M + 3) → ∀ (c : ℕ → Option Bool), c 0 = none →
    ∀ w, 1 ≤ w → w < M + 3 → ∀ b : Bool,
      Derivable (theory (M + 3))
        (drawn [mc (M + 3) .box [0] (setCtl c w (some b)), mc (M + 3) .box [0] (setCtl c w (some !b))])
        (mc (M + 3) .box [0] (setCtl c w none)) := by
  intro M
  induction M with
  | zero =>
    intro ih
    exact merge_step (N' := 2) (by omega) ih fun c' hc' w' h1 h2 b => by
      obtain rfl : w' = 1 := by omega
      exact merge2 (ih 2 (by omega)) c' hc' b
  | succ M ihM =>
    intro ih
    exact merge_step (N' := M + 3) (by omega) ih (ihM (ih.mono (by omega)))

/-! ## Drawn products -/

theorem drawn_forall2 {N : ℕ} : ∀ {l l' : List (Circ N)},
    List.Forall₂ (fun A B => Derivable (theory N) A B) l l' →
      Derivable (theory N) (drawn l) (drawn l')
  | [], [], _ => Derivable.refl _
  | _ :: _, _ :: _, List.Forall₂.cons h hl => by
    rw [drawn_cons, drawn_cons]; exact dmul (drawn_forall2 hl) h

theorem drawn_map_congr {N : ℕ} {α : Type*} (l : List α) {f g : α → Circ N}
    (h : ∀ a ∈ l, Derivable (theory N) (f a) (g a)) :
    Derivable (theory N) (drawn (l.map f)) (drawn (l.map g)) := by
  apply drawn_forall2
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
    exact List.Forall₂.cons (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem drawn_flatMap {N : ℕ} {α : Type*} (l : List α) (g : α → List (Circ N)) :
    drawn (l.flatMap g) = drawn (l.map fun a => drawn (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, drawn_append, ih, List.map_cons, drawn_cons]

theorem range_double {β : Type*} (K : ℕ) (f : ℕ → β) :
    (List.range (2 * K)).map f = (List.range K).flatMap fun i => [f (2 * i), f (2 * i + 1)] := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append,
      List.map_append, ih, List.range_succ, List.flatMap_append]
    simp

/-- An equation between gates at canonical positions, moved by the frame of
the wires `ps`: each factor is identified with a moved canonical one. -/
theorem via_frame {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    {l r L R : List (Circ N)}
    (hl : List.Forall₂ (fun A B => Derivable (theory N) (placedBy N (netOf ps) A) B) l L)
    (hr : List.Forall₂ (fun A B => Derivable (theory N) (placedBy N (netOf ps) A) B) r R)
    (h : Derivable (theory N) (drawn l) (drawn r)) : Derivable (theory N) (drawn L) (drawn R) := by
  have h' := frame_eq (netOf_ok hnd hps) h
  have m : ∀ {l L : List (Circ N)},
      List.Forall₂ (fun A B => Derivable (theory N) (placedBy N (netOf ps) A) B) l L →
      Derivable (theory N) (drawn (l.map (placedBy N (netOf ps)))) (drawn L) := by
    intro l L hl
    apply drawn_forall2
    induction hl with
    | nil => exact List.Forall₂.nil
    | cons h _ ih => exact List.Forall₂.cons h ih
  exact ((m hl).symm.trans h').trans (m hr)

/-! ## (309) at any box wire -/

theorem frm_pos (ps : List ℕ) (q : ℕ) : frm ps (pos (netOf ps) q) = q := pos_reverse _ q

theorem setCtl_frm (ps : List ℕ) (c : ℕ → Option Bool) (w : ℕ) (v : Option Bool) :
    setCtl c w v ∘ frm ps = setCtl (c ∘ frm ps) (pos (netOf ps) w) v := by
  funext j
  simp only [Function.comp, setCtl]
  have : frm ps j = w ↔ j = pos (netOf ps) w := by
    constructor
    · rintro rfl; exact (pos_frm ps j).symm
    · rintro rfl; exact frm_pos ps w
  by_cases h : j = pos (netOf ps) w
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun e => h (this.1 e)), if_neg h]

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

/-- The controls `base` with the bits of `i` on the wires `ws` (the first wire
the least significant bit). -/
def bitsOn : List ℕ → ℕ → (ℕ → Option Bool) → ℕ → Option Bool
  | [], _, base => base
  | w :: ws, i, base => setCtl (bitsOn ws (i / 2) base) w (some (decide (i % 2 = 1)))

/-- The controls `base` with the wires `ws` idle. -/
def idleOn : List ℕ → (ℕ → Option Bool) → ℕ → Option Bool
  | [], base => base
  | w :: ws, base => idleOn ws (setCtl base w none)

theorem bitsOn_of_not_mem : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) (j : ℕ), j ∉ ws →
    bitsOn ws i base j = base j
  | [], _, _, _, _ => rfl
  | w :: ws, i, base, j, hj => by
    have hjw : j ≠ w := fun e => hj (by simp [e])
    simp only [bitsOn, setCtl, hjw, if_false]
    exact bitsOn_of_not_mem ws _ base j (fun h => hj (by simp [h]))

theorem setCtl_bitsOn : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) (w : ℕ) (v : Option Bool),
    w ∉ ws → setCtl (bitsOn ws i base) w v = bitsOn ws i (setCtl base w v)
  | [], _, _, _, _, _ => rfl
  | u :: ws, i, base, w, v, hw => by
    have hwu : w ≠ u := fun e => hw (by simp [e])
    simp only [bitsOn]
    rw [← setCtl_bitsOn ws (i / 2) base w v (fun h => hw (by simp [h]))]
    funext j
    simp only [setCtl]
    by_cases h1 : j = w <;> by_cases h2 : j = u <;> simp_all

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
