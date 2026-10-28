/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The multi-controlled `H` as the box between two `P ⊗ P`

Definition 2.4 writes the canonical multi-controlled `H` with `k ≥ 2`
controls as `P ⊗ P`, the box with one more control, `P ⊗ P` (`mch`).  Placed
on the wires `0, 1` (box wire, `H` wire) and controls above, with any
colours, this stays true (`hgPP`): the swap network of the placement and the
`X` gates of the colours act on the wires `2, …` and commute with the `P ⊗ P`
on the wires `0, 1`.
-/
import QCert.RealCliffordCH.Sec8.D.N8.Kit

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng Net

theorem range_two (N : ℕ) (hN : 2 ≤ N) : List.range N = 0 :: 1 :: List.range' 2 (N - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [List.range_eq_range', show n + 2 - 2 = n by omega]
  show List.range' 0 (n + 1 + 1) = _
  rw [List.range'_succ, List.range'_succ]

/-- The controls of the box version: wire `1` and those of the `H`. -/
theorem ctrlWires_hg_box (N : ℕ) (hN : 2 ≤ N) (c : ℕ → Option Bool) :
    ctrlWires N [0] (setCtl c 1 (some true)) = 1 :: ctrlWires N [0, 1] c := by
  unfold ctrlWires
  rw [range_two N hN]
  have hr : (List.range' 2 (N - 2)).filter
      (fun j => (setCtl c 1 (some true) j).isSome && !([0].contains j)) =
      (List.range' 2 (N - 2)).filter (fun j => (c j).isSome && !([0, 1].contains j)) := by
    refine List.filter_congr (fun j hj => ?_)
    rw [List.mem_range'_1] at hj
    have h1 : j ≠ 1 := by omega
    have h0 : (j == 0) = false := by simp; omega
    have h1' : (j == 1) = false := by simp; omega
    simp [setCtl, h1, h0, h1']
  simp only [List.filter_cons, hr]
  simp [setCtl]

theorem whiteWires_hg_box (N : ℕ) (hN : 2 ≤ N) (c : ℕ → Option Bool) :
    whiteWires N [0] (setCtl c 1 (some true)) = whiteWires N [0, 1] c := by
  unfold whiteWires
  rw [range_two N hN]
  have hr : (List.range' 2 (N - 2)).filter
      (fun j => setCtl c 1 (some true) j == some false && !([0].contains j)) =
      (List.range' 2 (N - 2)).filter (fun j => c j == some false && !([0, 1].contains j)) := by
    refine List.filter_congr (fun j hj => ?_)
    rw [List.mem_range'_1] at hj
    have h1 : j ≠ 1 := by omega
    have h0 : (j == 0) = false := by simp; omega
    have h1' : (j == 1) = false := by simp; omega
    simp [setCtl, h1, h0, h1']
  simp only [List.filter_cons, hr]
  simp [setCtl]

theorem atBot_atBot : ∀ (N : ℕ) {m M : ℕ} (g : Circ m), m ≤ M → M ≤ N →
    atBot N (atBot M g) = atBot N g
  | 0, m, M, g, h1, h2 => by simp [atBot]
  | N + 1, m, M, g, h1, h2 => by
    by_cases e : M = N + 1
    · subst e; rw [atBot_self]
    · rw [atBot_succ N _ e, atBot_succ N g (by omega), atBot_atBot N g h1 (by omega)]

theorem atBot_pp (N k : ℕ) (hk : k + 2 ≤ N) :
    atBot N (pp : Circ (k + 2)) = ppAt N 0 1 := by
  have e1 : (pp : Circ (k + 2)) = atBot (k + 2) (pp : Circ 2) := by
    rw [← MS.pad_pp k, pad_atBot2]
  rw [e1, atBot_atBot N (pp : Circ 2) (by omega) hk, ppAt, placeG_pair N _ (by omega)]

/-- The swaps of the placement on `0 :: 1 :: cs` act on the wires `2, …`. -/
theorem netK_ge2 (cs : List ℕ) : ∀ n, ∀ x ∈ netK (0 :: 1 :: cs) n, 2 ≤ x
  | 0 => by simp [netK]
  | n + 1 => by
    intro x hx
    rw [netK, List.mem_append] at hx
    rcases hx with hx | hx
    · exact netK_ge2 cs n x hx
    · rcases n with _ | _ | n
      · simp [curPos, run] at hx
      · simp [curPos, run] at hx
      · exact le_trans (by omega) (mem_run hx).1

theorem highW_mono {n a b : ℕ} {v : Circ n} (h : HighW b v) (hab : a ≤ b) : HighW a v :=
  fun g hg => le_trans hab (h g hg)

theorem highW_xs (N : ℕ) : ∀ (ws : List ℕ), (∀ j ∈ ws, 2 ≤ j) → HighW 2 (drawn (ws.map (xAt N)))
  | [], _ => by intro g hg; simp [drawn] at hg
  | j :: ws, h => by
    rw [List.map_cons, Net.drawn_cons]
    exact highW_mul (highW_xs N ws (fun x hx => h x (by simp [hx])))
      (highW_mono (xAt_wires N j).2 (h j (by simp)))

theorem lowW_ppAt (N : ℕ) (hN : 2 ≤ N) : LowW 2 (ppAt N 0 1) := by
  rw [ppAt, placeG_pair N _ hN]; exact lowW_atBot N _

/-- `P` commutes with `A`, `A` acting on the wires `2, …`. -/
theorem pp_comm {N : ℕ} (hN : 2 ≤ N) {A : Circ N} (hA : HighW 2 A) :
    Derivable (theory N) (A * ppAt N 0 1) (ppAt N 0 1 * A) :=
  comm_low_high _ _ (lowW_ppAt N hN) hA

/-- The multi-controlled `H` on the wires `0, 1` with at least two controls is
the box on wire `0` with one more control on wire `1`, between two `P ⊗ P`. -/
theorem hgPP (N : ℕ) (hN : 2 ≤ N) (c : ℕ → Option Bool)
    (hk : 2 ≤ (ctrlWires N [0, 1] c).length) :
    Derivable (theory N) (mc N .hg [0, 1] c)
      (drawn [ppAt N 0 1, mc N .box [0] (setCtl c 1 (some true)), ppAt N 0 1]) := by
  set cs := ctrlWires N [0, 1] c with hcs
  set ws := whiteWires N [0, 1] c with hws
  obtain ⟨k, hkk⟩ : ∃ k, cs.length = k + 2 := ⟨cs.length - 2, by omega⟩
  have hcsN : ∀ j ∈ cs, 2 ≤ j ∧ j < N := by
    intro j hj
    simp only [hcs, ctrlWires, List.mem_filter, List.mem_range, Bool.and_eq_true,
      Bool.not_eq_true', List.contains_cons, List.contains_nil, Bool.or_eq_false_iff] at hj
    refine ⟨?_, hj.1⟩
    have h0 := hj.2.2.1; have h1 := hj.2.2.2.1
    simp at h0 h1; omega
  have hwsN : ∀ j ∈ ws, 2 ≤ j := by
    intro j hj
    simp only [hws, whiteWires, List.mem_filter, List.mem_range, Bool.and_eq_true,
      Bool.not_eq_true', List.contains_cons, List.contains_nil, Bool.or_eq_false_iff] at hj
    have h0 := hj.2.2.1; have h1 := hj.2.2.2.1
    simp at h0 h1; omega
  have hlenN : k + 4 ≤ N := by
    have hnd : (0 :: 1 :: cs).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ?_⟩⟩
      · intro h; rcases List.mem_cons.1 h with h | h
        · omega
        · have := (hcsN 0 h).1; omega
      · intro h; have := (hcsN 1 h).1; omega
      · exact (List.nodup_range).filter _
    have := length_le_of_lt (M := N) hnd (fun p hp => by
      rcases List.mem_cons.1 hp with rfl | hp
      · omega
      rcases List.mem_cons.1 hp with rfl | hp
      · omega
      exact (hcsN p hp).2)
    simp only [List.length_cons] at this; omega
  -- the two gates as placements
  have eH : mc N .hg [0, 1] c = colourW N ws (placeG N (mch cs.length) (0 :: 1 :: cs)) := rfl
  have eB : mc N .box [0] (setCtl c 1 (some true)) =
      colourW N ws (placeG N (box (cs.length + 1)) (0 :: 1 :: cs)) := by
    unfold mc
    rw [ctrlWires_hg_box N hN c, whiteWires_hg_box N hN c]
    rfl
  rw [eH, eB]
  set μ := netK (0 :: 1 :: cs) (0 :: 1 :: cs).length
  have hμ : HighW 2 (swW N μ) := highW_swW μ (netK_ge2 cs _)
  have hμr : HighW 2 (swW N μ.reverse) :=
    highW_swW μ.reverse (fun x hx => netK_ge2 cs _ x (List.mem_reverse.1 hx))
  have hX : HighW 2 (drawn (ws.map (xAt N))) := highW_xs N ws hwsN
  have emch : mch cs.length = drawn [pp, box (cs.length + 1), pp] := by
    rw [hkk]; rfl
  rw [emch, placeG_eq, placeG_eq, atBot_drawn]
  simp only [List.map_cons, List.map_nil]
  rw [atBot_pp N cs.length (by omega)]
  set P := ppAt N 0 1
  set Bb := atBot N (box (cs.length + 1))
  rw [Net.colourW_eq, Net.colourW_eq]
  set X := drawn (ws.map (xAt N))
  simp only [placedBy, drawn, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  -- move both `P` outwards
  have cX := pp_comm hN hX
  have cμ := pp_comm hN hμ
  have cμr := pp_comm hN hμr
  -- X * (μr * (P * (Bb * P)) * μ) * X  ≈  P * (X * (μr * Bb * μ) * X) * P
  have s1 : Derivable (theory N) (swW N μ.reverse * (P * (Bb * P)) * swW N μ)
      (P * (swW N μ.reverse * Bb * swW N μ) * P) := by
    have e1 : swW N μ.reverse * (P * (Bb * P)) * swW N μ =
        (swW N μ.reverse * P) * Bb * (P * swW N μ) := by simp only [mul_assoc]
    rw [e1]
    refine (dmul (dmul cμr (Derivable.refl Bb)) cμ.symm).trans ?_
    simp only [mul_assoc]; exact Derivable.refl _
  have s2 : Derivable (theory N) (X * (P * (swW N μ.reverse * Bb * swW N μ) * P) * X)
      (P * (X * (swW N μ.reverse * Bb * swW N μ) * X) * P) := by
    have e1 : X * (P * (swW N μ.reverse * Bb * swW N μ) * P) * X =
        (X * P) * (swW N μ.reverse * Bb * swW N μ) * (P * X) := by simp only [mul_assoc]
    rw [e1]
    refine (dmul (dmul cX (Derivable.refl _)) cX.symm).trans ?_
    simp only [mul_assoc]; exact Derivable.refl _
  refine (dright X (dleft X s1)).trans ?_
  refine s2.trans ?_
  simp only [mul_assoc]; exact Derivable.refl _

end QCert.RealCliffordCH.Sec8.D.N8
