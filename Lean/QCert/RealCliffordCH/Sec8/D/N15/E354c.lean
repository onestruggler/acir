/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (354): the statement

The `XZ` on the top wire as the inverse of the `ZX` (Lemma B.5, (317)), the
core from four wires on, (136) and (137) on three, and the statement.
-/
import QCert.RealCliffordCH.Sec8.D.N15.E354b

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-- The `XZ` merges on the top wire when the `ZX` does (Lemma B.5): its
merged and unmerged gates are the inverses of those of the `ZX`. -/
theorem P354_xz_top {M : ℕ} (hM : 2 ≤ M) (ih : IH (M + 1))
    (hc : ∀ x, Derivable (theory M)
      (drawn [mc M .xz [0] (colOn 1 M x), mc M .zx [0] (colOn 1 M x)]) 1)
    {x : ℕ → Bool} (h : P354 (M + 1) false x M) : P354 (M + 1) true x M := by
  intro b
  set C := fun v => setCtl (colOn 1 (M + 1) x) M v
  have hZ := h (!b)
  rw [Bool.not_not] at hZ
  rw [drawn_two'] at hZ
  -- the gates with full controls: (317)
  have full : ∀ c : Bool, Derivable (theory (M + 1))
      (mc (M + 1) (Kind.sgnZX true) [0] (C (some c)) * mc (M + 1) (Kind.sgnZX false) [0] (C (some c))) 1 := by
    intro c
    have h317 := (D.eq317 (M + 1) (by omega) ih (fun i => if i = M then c else x i)).1
    rw [drawn_two'] at h317
    have e : ∀ K, mc (M + 1) K [0] (colOn 1 (M + 1) (fun i => if i = M then c else x i)) =
        mc (M + 1) K [0] (C (some c)) := fun K => Net.mc_congr _ _ _ (fun i hi => by
      simp only [C, setCtl, colOn]
      by_cases hiM : i = M
      · subst hiM; simp; omega
      · simp [hiM])
    rwa [e, e] at h317
  -- the gates idle on the top wire: (317) one wire down
  have idle : Derivable (theory (M + 1))
      (mc (M + 1) (Kind.sgnZX false) [0] (C none) * mc (M + 1) (Kind.sgnZX true) [0] (C none)) 1 := by
    have h1 := derivable_padTop (hc x)
    rw [drawn_two', map_mul, map_one] at h1
    have e : ∀ K : Kind, kindSp K = 1 → padTop (mc M K [0] (colOn 1 M x)) = mc (M + 1) K [0] (C none) := by
      intro K hK
      rw [← mc_top M K [0] _ (by simp [hK]) (by simp) (by simp; omega) (by simp [colOn])]
      exact Net.mc_congr _ _ _ (fun i hi => by
        simp only [C, setCtl, colOn]
        by_cases hiM : i = M
        · subst hiM; simp
        · rw [if_neg hiM]; split_ifs <;> first | rfl | omega)
    rw [e .zx rfl, e .xz rfl] at h1
    exact h1
  have := inv_merge hZ (full b) (full (!b)) idle
  rw [drawn_two']
  exact this

/-- (317) for the `ZX` and `XZ` on two wires, by completeness. -/
theorem inv2 (ih : IH 3) (x : ℕ → Bool) :
    Derivable (theory 2) (drawn [mc 2 .xz [0] (colOn 1 2 x), mc 2 .zx [0] (colOn 1 2 x)]) 1 := by
  have e : ∀ K, mc 2 K [0] (colOn 1 2 x) = mc 2 K [0] (fun i => if i = 1 then some (x 1) else none) :=
    fun K => Net.mc_congr _ _ _ (fun i hi => by
      rcases i with _ | _ | i
      · simp [colOn]
      · simp [colOn]
      · omega)
  rw [e, e]
  cases x 1
  · exact ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))
  · exact ih 2 (by omega) _ _ (Fast.sem_of_fast (by decide +kernel))

/-- (354) from four wires on, on the top wire. -/
theorem P354_top4 {m : ℕ} (ih : IH (m + 4)) (a : Bool) (x : ℕ → Bool) :
    P354 (m + 4) a x (m + 3) := by
  have h0 : P354 (m + 4) false (fun _ => true) (m + 3) := by
    intro b
    have e : ∀ v, mc (m + 4) (Kind.sgnZX false) [0] (setCtl (colOn 1 (m + 4) fun _ => true) (m + 3) v) =
        Zc m v := fun v => Net.mc_congr _ _ _ (fun i hi => by
      simp only [cZ, setCtl, colOn, blackOn])
    rw [e, e, e]
    exact merge_top_core ih b
  have hz := P354_all ih h0
  cases a
  · exact hz x
  · exact P354_xz_top (M := m + 3) (by omega) ih
      (fun y => (D.eq317 (m + 3) (by omega) (ih.mono (by omega)) y).2) (hz x)

set_option maxRecDepth 20000 in
/-- (136), (137): (354) on three wires, on the top wire, black on wire `1`. -/
theorem P354_three_core (ih : IH 3) : P354 3 false (fun _ => true) 2 := by
  have eW : ∀ v, mc 3 (Kind.sgnZX false) [0] (setCtl (colOn 1 3 fun _ => true) 2 v) =
      mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then v else none) :=
    fun v => Net.mc_congr _ _ _ (fun i hi => by
      rcases i with _ | _ | _ | i
      · simp [setCtl, colOn]
      · simp [setCtl, colOn]
      · simp [setCtl, colOn]
      · omega)
  intro b
  rw [eW, eW, eW]
  cases b
  · have h := d136 ih
    have e1 : l136 = drawn [mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then some false else none),
        mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then some true else none)] := by
      rfl
    have e2 : r136 = mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then none else none) := by
      rfl
    rw [e1, e2] at h
    exact h
  · have h := d137 ih
    have e1 : l137 = drawn [mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then some true else none),
        mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then some false else none)] := by
      rfl
    have e2 : r137 = mc 3 .zx [0] (fun i => if i = 1 then some true else if i = 2 then none else none) := by
      rfl
    rw [e1, e2] at h
    exact h

/-- (354) on three wires, on the top wire. -/
theorem P354_top3 (ih : IH 3) (a : Bool) (x : ℕ → Bool) : P354 3 a x 2 := by
  have hz := P354_all ih (P354_three_core ih)
  cases a
  · exact hz x
  · exact P354_xz_top (M := 2) le_rfl ih (inv2 ih) (hz x)

/-- (354): a black and a white control of a multi-controlled `(-1)ᵃ ZX` on the
same wire `w` merge (in either order, `b` the colour of the first). -/
theorem eq354 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (a : Bool) (x : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w)
    (hwN : w < N) (b : Bool) :
    Derivable (theory N)
      (drawn [mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some b)),
        mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w (some !b))])
      (mc N (Kind.sgnZX a) [0] (setCtl (colOn 1 N x) w none)) := by
  have htop : ∀ y, P354 N a y (N - 1) := by
    intro y
    rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
    · exact P354_top3 ih a y
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
      exact P354_top4 ih a y
  exact P354_any ih htop w hw hwN x b

end QCert.RealCliffordCH.Sec8.D.N15
