/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (355): the square of the multi-controlled `XZ` is the box

The paper's proof.  Every control black and `XZ` first: by (305) the box is
`XZ₂ · B · ZX₂ · B` with `XZ₂`, `ZX₂` the `XZ`, `ZX` controlled by wire `1`
alone and `B` the box on wire `1`; by (354) over every colouring of the
wires `2, …` (`mergeListZ`) `XZ₂` and `ZX₂` are products of `XZ`s and `ZX`s
with every control, and those with a white control pass `B` ((347)), pass the
others ((351)) and cancel pairwise ((317)), leaving `XZ · B · ZX · B`, which
is `XZ · XZ` by (333), (334) and (311) (`xz_sq`).  The `ZX` as the inverse of
the `XZ` ((317), (299)); the colours by (81).
-/
import QCert.RealCliffordCH.Sec8.D.N15.MergeZ

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-! ## Colourings -/

/-- A property of colourings stable under (81) on the wires `1, …, N - 1`
other than `w` holds for every colouring when it holds for the black one. -/
theorem colour_ind {N w : ℕ} (Q : (ℕ → Bool) → Prop)
    (hcongr : ∀ x y : ℕ → Bool, (∀ i, 1 ≤ i → i < N → i ≠ w → x i = y i) → Q x → Q y)
    (hflip : ∀ (x : ℕ → Bool) (j : ℕ), 1 ≤ j → j < N → j ≠ w → Q x → Q (flip1 x j))
    (h0 : Q fun _ => true) : ∀ x, Q x := by
  have key : ∀ k, ∀ x : ℕ → Bool, (∀ i, k ≤ i → x i = true) → Q x := by
    intro k
    induction k with
    | zero => exact fun x hx => hcongr _ _ (fun i _ _ _ => (hx i (Nat.zero_le _)).symm) h0
    | succ k ihk =>
      intro x hx
      have hx' : ∀ i, k ≤ i → (fun i => if i = k then true else x i) i = true := by
        intro i hi
        by_cases hik : i = k
        · simp [hik]
        · simp only [if_neg hik]; exact hx i (by omega)
      by_cases hk : 1 ≤ k ∧ k < N ∧ k ≠ w
      · cases hxk : x k
        · have h1 := hflip _ k hk.1 hk.2.1 hk.2.2 (ihk _ hx')
          refine hcongr _ _ (fun i _ _ _ => ?_) h1
          simp only [flip1]
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · simp [hik]
        · refine hcongr _ _ (fun i _ _ _ => ?_) (ihk _ hx')
          by_cases hik : i = k
          · subst hik; simp [hxk]
          · simp [hik]
      · refine hcongr _ _ (fun i hi1 hiN hiw => ?_) (ihk _ hx')
        by_cases hik : i = k
        · subst hik; exact absurd ⟨hi1, hiN, hiw⟩ hk
        · simp [hik]
  intro x
  exact hcongr _ _ (fun i _ hiN _ => by simp [hiN])
    (key N (fun i => if i < N then x i else true) (fun i hi => by simp; omega))

/-! ## Products of commuting inverse pairs -/

/-- `∏ Aᵢ · ∏ Bᵢ = 1` when `Aᵢ Bᵢ = 1` and `Aᵢ` commutes with `Bⱼ`, `i ≠ j`. -/
theorem prod_cancel {N : ℕ} (A B : ℕ → Circ N) :
    ∀ n, (∀ i < n, ∀ j < n, i ≠ j → D.Comm N (A i) (B j)) →
      (∀ i < n, Derivable (theory N) (A i * B i) 1) →
      Derivable (theory N) (drawn ((List.range n).map A) * drawn ((List.range n).map B)) 1
  | 0, _, _ => by simpa [drawn] using Derivable.refl (Γ := theory N) 1
  | n + 1, hc, hi => by
    rw [List.range_succ, List.map_append, List.map_append, SE.drawn_append, SE.drawn_append]
    simp only [List.map_cons, List.map_nil, drawn_one']
    set P := drawn ((List.range n).map A)
    set Q := drawn ((List.range n).map B)
    have hPB : D.Comm N P (B n) := N13.comm_drawn_left _ (fun a ha => by
      obtain ⟨i, hi', rfl⟩ := List.mem_map.1 ha
      exact hc i (by simp at hi'; omega) n (by omega) (by simp at hi'; omega))
    unfold D.Comm at hPB
    rw [drawn_two', drawn_two'] at hPB
    have e : A n * P * (B n * Q) = A n * (P * B n) * Q := by simp only [mul_assoc]
    rw [e]
    refine (dright Q (dleft (A n) hPB.symm)).trans ?_
    have e2 : A n * (B n * P) * Q = (A n * B n) * (P * Q) := by simp only [mul_assoc]
    rw [e2]
    have h1 := hi n (by omega)
    have h2 := prod_cancel A B n (fun i hi j hj hij => hc i (by omega) j (by omega) hij)
      (fun i hi' => hi i (by omega))
    simpa using dmul h1 h2

/-! ## The bits of a colouring index -/

theorem bitsOn_mem (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool) :
    ∀ j ∈ ws, ∃ b, bitsOn ws i base j = some b := by
  induction ws generalizing i with
  | nil => intro j hj; simp at hj
  | cons w ws ihw =>
    intro j hj
    simp only [bitsOn, setCtl]
    by_cases hjw : j = w
    · exact ⟨_, by rw [if_pos hjw]⟩
    · rw [if_neg hjw]; exact ihw (i / 2) j (by simpa [hjw] using hj)

/-- Below the last index some wire of `ws` is white. -/
theorem bitsOn_white : ∀ (ws : List ℕ) (i : ℕ) (base : ℕ → Option Bool), ws.Nodup →
    i + 1 < 2 ^ ws.length → ∃ j ∈ ws, bitsOn ws i base j = some false
  | [], i, _, _, h => by simp at h
  | w :: ws, i, base, hnd, h => by
    have hnd' := List.nodup_cons.1 hnd
    by_cases hi : i % 2 = 1
    · obtain ⟨j, hj, hb⟩ := bitsOn_white ws (i / 2) base hnd'.2 (by
        rw [List.length_cons, pow_succ] at h; omega)
      refine ⟨j, by simp [hj], ?_⟩
      have hjw : j ≠ w := fun e => hnd'.1 (e ▸ hj)
      simp only [bitsOn, setCtl, if_neg hjw]; exact hb
    · exact ⟨w, by simp, by simp [bitsOn, setCtl, hi]⟩

theorem bitsOn_last : ∀ (ws : List ℕ) (base : ℕ → Option Bool) (j : ℕ), j ∈ ws →
    bitsOn ws (2 ^ ws.length - 1) base j = some true
  | [], _, j, hj => by simp at hj
  | w :: ws, base, j, hj => by
    simp only [bitsOn, setCtl, List.length_cons]
    have e1 : (2 ^ (ws.length + 1) - 1) % 2 = 1 := by
      have := Nat.one_le_two_pow (n := ws.length); rw [pow_succ]; omega
    have e2 : (2 ^ (ws.length + 1) - 1) / 2 = 2 ^ ws.length - 1 := by
      have := Nat.one_le_two_pow (n := ws.length); rw [pow_succ]; omega
    by_cases hjw : j = w
    · rw [if_pos hjw]; simp [e1]
    · rw [if_neg hjw, e2]; exact bitsOn_last ws base j (by simpa [hjw] using hj)

end QCert.RealCliffordCH.Sec8.D.N15
