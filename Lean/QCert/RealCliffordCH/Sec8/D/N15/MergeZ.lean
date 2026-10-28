/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (354) with idle wires, and over every colouring of a list of wires

As `E/TransportCore.mergeC` for the box: with an idle wire other than the
merged one, the merge is (354) one wire down (`Net.liftIdle`), so by induction
on the width (354) holds for any controls (`mergeCZ`; on two wires it is
decided); iterated over the colourings of a list of wires (`mergeListZ`), the
multi-controlled `(-1)ᵃ ZX` with those wires idle is the product of its
versions with every colouring of them.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E354c

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

theorem kindSp_sgnZX (a : Bool) : kindSp (Kind.sgnZX a) = 1 := by cases a <;> rfl

/-- (354) on two wires, decided. -/
theorem merge2Z (ih2 : CompleteAt 2) (a : Bool) (c : ℕ → Option Bool) (hc : c 0 = none)
    (b : Bool) :
    Derivable (theory 2) (drawn [mc 2 (Kind.sgnZX a) [0] (setCtl c 1 (some b)),
      mc 2 (Kind.sgnZX a) [0] (setCtl c 1 (some !b))]) (mc 2 (Kind.sgnZX a) [0] (setCtl c 1 none)) := by
  have e : ∀ v, mc 2 (Kind.sgnZX a) [0] (setCtl c 1 v) =
      mc 2 (Kind.sgnZX a) [0] (fun j => if j = 1 then v else none) := by
    intro v
    apply Net.mc_congr
    intro i hi
    rcases i with _ | _ | i
    · simp [setCtl, hc]
    · simp [setCtl]
    · omega
  rw [e, e, e]
  cases a <;> cases b
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))
  · exact ih2 _ _ (Fast.sem_of_fast (by decide +kernel))

/-- One step of the induction: (354) with idle wires on `N' + 1` wires, given it
on `N'` wires. -/
theorem merge_stepZ {N' : ℕ} (hN : 3 ≤ N' + 1) (ih : IH (N' + 1)) (a : Bool)
    (down : ∀ c' : ℕ → Option Bool, c' 0 = none → ∀ w', 1 ≤ w' → w' < N' → ∀ b : Bool,
      Derivable (theory N')
        (drawn [mc N' (Kind.sgnZX a) [0] (setCtl c' w' (some b)),
          mc N' (Kind.sgnZX a) [0] (setCtl c' w' (some !b))])
        (mc N' (Kind.sgnZX a) [0] (setCtl c' w' none)))
    (c : ℕ → Option Bool) (hc : c 0 = none) (w : ℕ) (hw1 : 1 ≤ w) (hw2 : w < N' + 1) (b : Bool) :
    Derivable (theory (N' + 1))
      (drawn [mc (N' + 1) (Kind.sgnZX a) [0] (setCtl c w (some b)),
        mc (N' + 1) (Kind.sgnZX a) [0] (setCtl c w (some !b))])
      (mc (N' + 1) (Kind.sgnZX a) [0] (setCtl c w none)) := by
  by_cases hq : ∃ q, 1 ≤ q ∧ q < N' + 1 ∧ q ≠ w ∧ c q = none
  · obtain ⟨q, hq1, hq2, hqw, hcq⟩ := hq
    have hA : ∀ v, ToTop N' q (mc (N' + 1) (Kind.sgnZX a) [0] (setCtl c w v))
        (mc N' (Kind.sgnZX a) [0] (setCtl (c ∘ liftW q) (dropW q w) v)) := by
      intro v
      have := ToTop.mc (M := N') (q := q) (by omega) (Kind.sgnZX a) [0] (setCtl c w v)
        (by simp [kindSp_sgnZX]) (by simp) (by simp) (by simp; omega) (by simp [setCtl, hqw, hcq])
      have e0 : [0].map (dropW q) = [0] := by simp [dropW]
      rwa [setCtl_liftW (Ne.symm hqw), e0] at this
    have hc' : (c ∘ liftW q) 0 = none := by simp [liftW, show 0 < q by omega, hc]
    have hw' : 1 ≤ dropW q w ∧ dropW q w < N' := by simp only [dropW]; split_ifs <;> omega
    exact liftIdle (ToTop.ofList (List.Forall₂.cons (hA _) (List.Forall₂.cons (hA _)
      List.Forall₂.nil))) (hA none) (down (c ∘ liftW q) hc' (dropW q w) hw'.1 hw'.2 b)
  · push Not at hq
    set x : ℕ → Bool := fun j => (c j).getD false
    have e : ∀ v, mc (N' + 1) (Kind.sgnZX a) [0] (setCtl c w v) =
        mc (N' + 1) (Kind.sgnZX a) [0] (setCtl (colOn 1 (N' + 1) x) w v) := by
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
    exact eq354 (N' + 1) hN ih a x w hw1 hw2 b

/-- (354) on the target wire `0` for any controls (some wires may be idle). -/
theorem mergeCZ : ∀ (M : ℕ), IH (M + 3) → ∀ (a : Bool) (c : ℕ → Option Bool), c 0 = none →
    ∀ w, 1 ≤ w → w < M + 3 → ∀ b : Bool,
      Derivable (theory (M + 3))
        (drawn [mc (M + 3) (Kind.sgnZX a) [0] (setCtl c w (some b)),
          mc (M + 3) (Kind.sgnZX a) [0] (setCtl c w (some !b))])
        (mc (M + 3) (Kind.sgnZX a) [0] (setCtl c w none)) := by
  intro M
  induction M with
  | zero =>
    intro ih a
    exact merge_stepZ (N' := 2) (by omega) ih a fun c' hc' w' h1 h2 b => by
      obtain rfl : w' = 1 := by omega
      exact merge2Z (ih 2 (by omega)) a c' hc' b
  | succ M ihM =>
    intro ih a
    exact merge_stepZ (N' := M + 3) (by omega) ih a (ihM (ih.mono (by omega)) a)

/-- The multi-controlled `(-1)ᵃ ZX` on wire `0` over every colouring of the
wires `ws`, the other controls fixed, merge into the gate with the wires `ws`
idle. -/
theorem mergeListZ {M : ℕ} (ih : IH (M + 3)) (a : Bool) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → 0 ∉ ws → (∀ w ∈ ws, w < M + 3) →
      base 0 = none →
      Derivable (theory (M + 3))
        (drawn ((List.range (2 ^ ws.length)).map fun i =>
          mc (M + 3) (Kind.sgnZX a) [0] (bitsOn ws i base)))
        (mc (M + 3) (Kind.sgnZX a) [0] (idleOn ws base))
  | [], base, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil, drawn_one',
      bitsOn, idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, htw, hws, hb => by
    have hnd' := List.nodup_cons.1 hnd
    have hwt : w ≠ 0 := fun e => htw (by simp [e])
    have ih' := mergeListZ ih a ws (setCtl base w none) hnd'.2 (fun h => htw (by simp [h]))
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
    exact mergeCZ M ih a (bitsOn ws i base) hct w (by omega) (hws w (by simp)) false

end QCert.RealCliffordCH.Sec8.D.N15
