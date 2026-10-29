/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (353) inside package (v)

The multi-controlled `(-1)ᵃ ZX` with every control black commutes with the
swap of two of its controls, at every width from three.  This is the
argument of `D/N15/E353*` (which cannot be imported here: `D/N15` uses
`N13`), with (333), (339) and (317) as hypotheses supplied by `N13.lean`.

* Swaps of the wires `j, j + 1`, `j ≥ 2`: Definition 2.4 writes the gate as
  `CH · B' · CH · B'`, `B'` the box on wire `1`; the `CH` and the swap of the
  wires `0, 1` are below the swap, and the box passes it by (307).
* On three wires the swap of the wires `1, 2` is (127).
* From four wires on, the swap of the wires `1, 2`: by (333) and the previous
  case the gate is `H' B H' B` with `H'` the multi-controlled `H` with its box
  on wire `3`; `B` is the product of its versions idle and white on wire `2`
  ((309)), the white one passes `H'` ((339)) and is an involution ((311)), so
  the gate is `H' Bᵢ H' Bᵢ` with `Bᵢ` idle on wire `2`, which the swap of the
  wires `1, 2` fixes ((313), and (274) for `Bᵢ`).

The result is `sym353`, the hypothesis `E.Sym353 N` of `E.mcSwapOf`: with it,
every multi-controlled gate, rotations included, moves along any swap
network.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E333

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

/-! ## Helpers (copies of `D/N15/Base`) -/

section Conj

variable {N : ℕ}

theorem drawn_one' (a : Circ N) : drawn [a] = a := by simp [drawn]

theorem drawn_two' (a b : Circ N) : drawn [a, b] = b * a := by simp [drawn]

theorem drawn_four' (a b c d : Circ N) : drawn [a, b, c, d] = d * c * b * a := by
  simp [drawn, mul_assoc]

/-- Conjugating a drawn product by an involution conjugates each factor. -/
theorem iconj_drawn {u : Circ N} (hu : Derivable (theory N) (u * u) 1) :
    ∀ l : List (Circ N), Derivable (theory N) (u * drawn l * u) (drawn (l.map fun g => u * g * u))
  | [] => by simpa [drawn] using hu
  | a :: l => by
    rw [Net.drawn_cons, List.map_cons, Net.drawn_cons]
    exact (conj_mul hu).trans (dmul (iconj_drawn hu l) (Derivable.refl _))

/-- A gate fixed by conjugation with an involution commutes with it. -/
theorem comm_of_conj {u a : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (h : Derivable (theory N) (u * a * u) a) : D.Comm N a u := by
  unfold D.Comm
  rw [drawn_two', drawn_two']
  have h1 : Derivable (theory N) (u * a * (u * u)) (u * a) := by
    have := dleft (u * a) hu; rwa [mul_one] at this
  have h2 : Derivable (theory N) ((u * a * u) * u) (a * u) := dright u h
  rw [show u * a * (u * u) = (u * a * u) * u by simp only [mul_assoc]] at h1
  exact h1.symm.trans h2

/-- Conversely, a gate commuting with an involution is fixed by conjugation. -/
theorem conj_of_comm {u a : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (h : D.Comm N a u) : Derivable (theory N) (u * a * u) a := by
  unfold D.Comm at h
  rw [drawn_two', drawn_two'] at h
  have := dright u h
  refine this.trans ?_
  have e : a * u * u = a * (u * u) := by simp only [mul_assoc]
  rw [e]
  have := dleft a hu
  rwa [mul_one] at this

theorem conj3 (u a : Circ N) : drawn [u, a, u] = u * a * u := by simp [drawn, mul_assoc]

/-- An equation between drawn products, conjugated by an involution factor by
factor. -/
theorem via_conj {u : Circ N} (hu : Derivable (theory N) (u * u) 1)
    {l r L R : List (Circ N)}
    (hl : List.Forall₂ (fun A B => Derivable (theory N) (u * A * u) B) l L)
    (hr : List.Forall₂ (fun A B => Derivable (theory N) (u * A * u) B) r R)
    (h : Derivable (theory N) (drawn l) (drawn r)) : Derivable (theory N) (drawn L) (drawn R) := by
  have m : ∀ {l L : List (Circ N)},
      List.Forall₂ (fun A B => Derivable (theory N) (u * A * u) B) l L →
      Derivable (theory N) (u * drawn l * u) (drawn L) := by
    intro l L hl
    refine (iconj_drawn hu l).trans (drawn_forall2 ?_)
    induction hl with
    | nil => exact List.Forall₂.nil
    | cons h _ ih => exact List.Forall₂.cons h ih
  exact (m hl).symm.trans ((dctx u u h).trans (m hr))

end Conj

section Frames

variable {N : ℕ}

theorem frm_not_mem' {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {j : ℕ}
    (hj : ps.length ≤ j) : frm ps j ∉ ps := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  have h1 : frm ps i = ps[i] := by
    rw [frm_getD hnd hps hi]; simp [List.getD_eq_getElem?_getD, hi]
  have := frm_injective ps (h1.trans he)
  omega

/-- Outside the special wires `ps` the frame stays outside `ps`. -/
theorem frm_out' {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {j : ℕ}
    (hj : ps.length ≤ j) (hjN : j < N) : frm ps j ∉ ps ∧ frm ps j < N :=
  ⟨frm_not_mem' hnd hps hj, frm_lt hnd hps hjN⟩

/-- A frame, with the canonical colours given pointwise. -/
theorem frameAtK {P : Kind → Prop} (hsw : McSwapK N P) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (K : Kind) (hK : P K) (tg tg' : List ℕ) (c d : ℕ → Option Bool)
    (hl : tg.length = kindSp K) (htnd : tg.Nodup) (htN : ∀ t ∈ tg, t < N)
    (htg : tg.map (frm ps) = tg') (h : ∀ j < N, d j = c (frm ps j)) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg d)) (mc N K tg' c) := by
  rw [Net.mc_congr N K tg (c := d) (c' := c ∘ frm ps) h, ← htg]
  exact frameK hsw hnd hps K hK tg c hl htnd htN

end Frames

/-! ## The canonical gates -/

theorem mc_zx_canon (k : ℕ) : mc (k + 1) .zx [0] (blackOn 1 (k + 1)) = zx k :=
  mc_canon .zx k

theorem mc_box_canon (k : ℕ) : mc (k + 1) .box [0] (blackOn 1 (k + 1)) = box k :=
  mc_canon .box k

theorem lowW_ch (k : ℕ) : LowW 2 (ch : Circ (k + 2)) := by
  rw [← MS.pad_ch k]; exact lowW_pad _ le_rfl

theorem lowW_swap (k : ℕ) : LowW 2 (swap : Circ (k + 2)) := by
  rw [← MS.pad_swap k]; exact lowW_pad _ le_rfl

theorem highW_swAt {N j : ℕ} (hj : 2 ≤ j) : HighW 2 (swAt N j) :=
  fun g hg => le_trans hj ((swAt_wires N j).2 g hg)

/-! ## The swap of two controls above wire `1` -/

/-- (353) for the `ZX` and the swap of the wires `j, j + 1`, `j ≥ 2`. -/
theorem comm_zx_sw_ge2 (k : ℕ) (ih : IH (k + 1 + 1)) (j : ℕ) (hj : 2 ≤ j)
    (hjN : j + 2 ≤ k + 1 + 1) :
    D.Comm (k + 1 + 1) (mc (k + 1 + 1) .zx [0] (blackOn 1 (k + 1 + 1))) (swAt (k + 1 + 1) j) := by
  have hbox : D.Comm (k + 1 + 1) (box (k + 1)) (swAt (k + 1 + 1) j) := by
    have h := D.eq307 (k + 1 + 1) (by omega) ih j (by omega) hjN
    unfold D.Bx at h
    rw [mc_box_canon] at h
    exact h
  have hlow : ∀ g : Circ (k + 1 + 1), LowW 2 g → D.Comm (k + 1 + 1) g (swAt (k + 1 + 1) j) :=
    fun g hg => by unfold D.Comm; rw [drawn_two', drawn_two']; exact comm_low_high g _ hg (highW_swAt hj)
  have hB : D.Comm (k + 1 + 1) (conj swap (box (k + 1))) (swAt (k + 1 + 1) j) := by
    have := N13.comm_drawn [swap, box (k + 1), swap] [swAt (k + 1 + 1) j] (fun a ha b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
      subst hb
      rcases ha with rfl | rfl | rfl
      · exact hlow _ (lowW_swap k)
      · exact hbox
      · exact hlow _ (lowW_swap k))
    rwa [drawn_one'] at this
  rw [mc_zx_canon]
  have := N13.comm_drawn [ch, conj swap (box (k + 1)), ch, conj swap (box (k + 1))]
    [swAt (k + 1 + 1) j] (fun a ha b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
      subst hb
      rcases ha with rfl | rfl | rfl | rfl
      · exact hlow _ (lowW_ch k)
      · exact hB
      · exact hlow _ (lowW_ch k)
      · exact hB)
  rwa [drawn_one'] at this

/-! ## Three wires: (127) -/

theorem comm_zx_sw_3 (ih : IH 3) :
    D.Comm 3 (mc 3 .zx [0] (blackOn 1 3)) (swAt 3 1) := by
  rw [show mc 3 .zx [0] (blackOn 1 3) = zx 2 from mc_zx_canon 2]
  have h := d127 ih
  unfold D.Comm
  simp only [l127, r127, circW, List.map, L.circ] at h
  convert h using 1 <;> simp [drawn, zx, box, conj, place2, MS.pad_ch, MS.pad_swap, mul_assoc]

/-! ## Four wires and more: the swap of the wires `1, 2` -/

section Four

variable (m : ℕ)

/-- The multi-controlled `H` of (333) with its box moved to wire `3`. -/
abbrev Hq : Circ (m + 4) :=
  mc (m + 4) .hg [3, 0] (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (blackOn 4 (m + 4))))
/-- The box of (333): box wire `1`, black on `0, 2, 3, …`. -/
abbrev Bq : Circ (m + 4) := mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4)))
/-- The same with wire `2` coloured `b`. -/
abbrev Bb (b : Bool) : Circ (m + 4) :=
  mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 b) (blackOn 3 (m + 4))))
/-- The same, idle on wire `2`. -/
abbrev Bi : Circ (m + 4) := mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4)))
/-- The box on wire `2`, black on `0, 3, …`, idle on wire `1`. -/
abbrev Bi' : Circ (m + 4) := mc (m + 4) .box [2] (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4)))

theorem Bb_true : Bb m true = Bq m := Net.mc_congr _ _ _ (fun j hj => by
  rcases j with _ | _ | _ | j <;> simp [ctlOr, ctlAt, blackOn] <;> omega)

variable {m} (ih : IH (m + 4))
include ih

theorem sw0_inv : Derivable (theory (m + 4)) (swAt (m + 4) 0 * swAt (m + 4) 0) 1 :=
  swsw (m + 4) 0 (by omega)

/-- A box on wire `0` moved to wire `1` by the swap of the wires `0, 1`. -/
theorem box01 (c d : ℕ → Option Bool) (hcd : ∀ j < m + 4, d j = c (Net.tau 0 j)) :
    Derivable (theory (m + 4)) (swAt (m + 4) 0 * mc (m + 4) .box [0] c * swAt (m + 4) 0)
      (mc (m + 4) .box [1] d) := by
  have h := mcSwapBH ih 0 (by omega) .box (Or.inl rfl) [0] c rfl (by simp) (by simp)
  rw [conj3] at h
  refine h.trans (der_of_eq ?_)
  rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
  exact Net.mc_congr _ _ _ (fun j hj => (hcd j hj).symm)

/-- (309) for the box on wire `1`, merged on wire `2`. -/
theorem merge_Bb (b : Bool) : Derivable (theory (m + 4)) (drawn [Bb m b, Bb m (!b)]) (Bi m) := by
  have h := D.eq309 (m + 4) (by omega) ih (fun _ => true) 2 (by omega) (by omega) b
  have k := via_conj (sw0_inv ih) (L := [Bb m b, Bb m (!b)]) (R := [Bi m])
    (List.Forall₂.cons (box01 ih _ _ ?_) (List.Forall₂.cons (box01 ih _ _ ?_) List.Forall₂.nil))
    (List.Forall₂.cons (box01 ih _ _ ?_) List.Forall₂.nil) (by rwa [drawn_one'])
  · rwa [drawn_one'] at k
  all_goals
    intro j hj
    rcases j with _ | _ | _ | j <;> simp [Net.tau, setCtl, colOn, ctlOr, ctlAt, blackOn] <;> omega

/-- (311) for the box on wire `1` white on wire `2`. -/
theorem inv_Bw : Derivable (theory (m + 4)) (drawn [Bb m false, Bb m false]) 1 := by
  have h := D.eq311 (m + 4) (by omega) ih (fun j => decide (j ≠ 2))
  have k := via_conj (sw0_inv ih) (L := [Bb m false, Bb m false]) (R := [])
    (List.Forall₂.cons (box01 ih _ _ ?_) (List.Forall₂.cons (box01 ih _ _ ?_) List.Forall₂.nil))
    List.Forall₂.nil (by simpa [drawn] using h)
  · simpa [drawn] using k
  all_goals
    intro j hj
    rcases j with _ | _ | _ | j <;> simp [Net.tau, colOn, ctlOr, ctlAt, blackOn] <;> omega

/-- (339): the box white on wire `2` passes `Hq`. -/
theorem comm_Hq_Bw
    (h339 : DiffOn 3 (m + 4) (fun j => decide (j ≠ 3)) (fun _ => true) →
      D.Comm (m + 4) (mc (m + 4) .box [0] (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true)
        (colOn 3 (m + 4) fun j => decide (j ≠ 3)))))
        (mc (m + 4) .hg [1, 2] (ctlOr (ctlAt 0 true) (colOn 3 (m + 4) fun _ => true)))) :
    D.Comm (m + 4) (Hq m) (Bb m false) := by
  have hsw := mcSwapBH ih
  have hnd : [1, 3, 0, 2].Nodup := by decide
  have hps : ∀ p ∈ [1, 3, 0, 2], p < m + 4 := by simp
  have f0 : frm [1, 3, 0, 2] 0 = 1 := frm_getD hnd hps (by simp)
  have f1 : frm [1, 3, 0, 2] 1 = 3 := frm_getD hnd hps (by simp)
  have f2 : frm [1, 3, 0, 2] 2 = 0 := frm_getD hnd hps (by simp)
  have f3 : frm [1, 3, 0, 2] 3 = 2 := frm_getD hnd hps (by simp)
  have hout : ∀ j, 4 ≤ j → j < m + 4 → 4 ≤ frm [1, 3, 0, 2] j ∧ frm [1, 3, 0, 2] j < m + 4 := by
    intro j hj hjN
    obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := j) (by simpa using hj) hjN
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hm
    exact ⟨by omega, hl⟩
  have fB : Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 3, 0, 2])
      (mc (m + 4) .box [0] (ctlOr (ctlAt 2 true) (ctlOr (ctlAt 1 true)
        (colOn 3 (m + 4) fun j => decide (j ≠ 3)))))) (Bb m false) := by
    refine frameAtK hsw hnd hps .box (Or.inl rfl) [0] [1] _ _ rfl (by simp) (by simp)
      (by simp [f0]) (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j
    · simp [ctlOr, ctlAt, colOn, blackOn, f0]
    · simp [ctlOr, ctlAt, colOn, blackOn, f1]
    · simp [ctlOr, ctlAt, colOn, blackOn, f2]
    · simp [ctlOr, ctlAt, colOn, blackOn, f3]
    · obtain ⟨h4, hl⟩ := hout (j + 1 + 1 + 1 + 1) (by omega) hj
      simp [ctlOr, ctlAt, colOn, blackOn, hj, hl, show 3 ≤ frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) by omega,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 0 by omega,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 2 by omega]
  have fH : Derivable (theory (m + 4)) (placedBy (m + 4) (netOf [1, 3, 0, 2])
      (mc (m + 4) .hg [1, 2] (ctlOr (ctlAt 0 true) (colOn 3 (m + 4) fun _ => true)))) (Hq m) := by
    refine frameAtK hsw hnd hps .hg (Or.inr rfl) [1, 2] [3, 0] _ _ rfl (by simp) (by simp)
      (by simp [f1, f2]) (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j
    · simp [ctlOr, ctlAt, colOn, blackOn, f0]
    · simp [ctlOr, ctlAt, colOn, blackOn, f1]
    · simp [ctlOr, ctlAt, colOn, blackOn, f2]
    · simp [ctlOr, ctlAt, colOn, blackOn, f3]
    · obtain ⟨h4, hl⟩ := hout (j + 1 + 1 + 1 + 1) (by omega) hj
      simp [ctlOr, ctlAt, colOn, blackOn, hj, hl, h4,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 1 by omega,
        show frm [1, 3, 0, 2] (j + 1 + 1 + 1 + 1) ≠ 2 by omega]
  have h := h339 ⟨3, le_rfl, by omega, by simp⟩
  have k := via_frame hnd hps (List.Forall₂.cons fB (List.Forall₂.cons fH List.Forall₂.nil))
    (List.Forall₂.cons fH (List.Forall₂.cons fB List.Forall₂.nil)) h
  exact k.symm

/-- (274): the box idle on wire `2` moves its box wire to wire `2`. -/
theorem Bi_eq : Derivable (theory (m + 4)) (Bi m) (Bi' m) := by
  have hsw := mcSwapBH ih
  have hnd : [2, 1, 0].Nodup := by decide
  have hps : ∀ p ∈ [2, 1, 0], p < m + 4 := by simp
  have f0 : frm [2, 1, 0] 0 = 2 := frm_getD hnd hps (by simp)
  have f1 : frm [2, 1, 0] 1 = 1 := frm_getD hnd hps (by simp)
  have f2 : frm [2, 1, 0] 2 = 0 := frm_getD hnd hps (by simp)
  have hpt : ∀ j < m + 4, blackOn 2 (m + 4) j =
      (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4))) (frm [2, 1, 0] j) := by
    intro j hj
    rcases j with _ | _ | _ | j
    · simp [ctlOr, ctlAt, blackOn, f0]
    · simp [ctlOr, ctlAt, blackOn, f1]
    · simp [ctlOr, ctlAt, blackOn, f2]
    · obtain ⟨hm, hl⟩ := frm_out' hnd hps (j := j + 1 + 1 + 1) (by simp) hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hm
      simp [ctlOr, ctlAt, blackOn, hj, hl, show 3 ≤ frm [2, 1, 0] (j + 1 + 1 + 1) by omega,
        show frm [2, 1, 0] (j + 1 + 1 + 1) ≠ 0 by omega]
  have f1' := frameAtK hsw hnd hps .box (Or.inl rfl) [1] [1] _ _ rfl (by simp) (by simp)
    (by simp [f1]) hpt
  have f0' := frameAtK hsw hnd hps .box (Or.inl rfl) [0] [2] _ _ rfl (by simp) (by simp)
    (by simp [f0]) hpt
  have h := D.eq274 (m + 4) (by omega) ih
  have k := via_frame hnd hps (l := [_]) (r := [_]) (List.Forall₂.cons f1' List.Forall₂.nil)
    (List.Forall₂.cons f0' List.Forall₂.nil) (by rwa [drawn_one', drawn_one'])
  rwa [drawn_one', drawn_one'] at k

/-- The `ZX` as `Hq Bq Hq Bq` ((333) and (353) for the wires `2, 3`). -/
theorem zx_Hq
    (h333 : Derivable (theory (m + 4)) (mc (m + 4) .zx [0] (blackOn 1 (m + 4)))
      (drawn [mc (m + 4) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))),
        mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4))),
        mc (m + 4) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))),
        mc (m + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4)))])) :
    Derivable (theory (m + 4)) (mc (m + 4) .zx [0] (blackOn 1 (m + 4)))
    (drawn [Hq m, Bq m, Hq m, Bq m]) := by
  have hsw := mcSwapBH ih
  have hS : Derivable (theory (m + 4)) (swAt (m + 4) 2 * swAt (m + 4) 2) 1 :=
    swsw (m + 4) 2 (by omega)
  have hZ : Derivable (theory (m + 4))
      (swAt (m + 4) 2 * mc (m + 4) .zx [0] (blackOn 1 (m + 4)) * swAt (m + 4) 2)
      (mc (m + 4) .zx [0] (blackOn 1 (m + 4))) :=
    conj_of_comm hS (comm_zx_sw_ge2 (m + 2) ih 2 le_rfl (by omega))
  have hH : Derivable (theory (m + 4))
      (swAt (m + 4) 2 * mc (m + 4) .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))) *
        swAt (m + 4) 2) (Hq m) := by
    have h := hsw 2 (by omega) .hg (Or.inr rfl) [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 4))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([2, 0] : List ℕ).map (Net.tau 2) = [3, 0] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have hB : Derivable (theory (m + 4)) (swAt (m + 4) 2 * Bq m * swAt (m + 4) 2) (Bq m) := by
    have h := hsw 2 (by omega) .box (Or.inl rfl) [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 4))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([1] : List ℕ).map (Net.tau 2) = [1] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have k := via_conj hS (l := [mc (m + 4) .zx [0] (blackOn 1 (m + 4))]) (L := [_])
    (List.Forall₂.cons hZ List.Forall₂.nil)
    (List.Forall₂.cons hH (List.Forall₂.cons hB (List.Forall₂.cons hH (List.Forall₂.cons hB
      List.Forall₂.nil)))) (by rw [drawn_one']; exact h333)
  rwa [drawn_one'] at k

/-- `Hq Bq Hq Bq = Hq Bi Hq Bi` ((309), (339), (311)). -/
theorem Hq_Bi (hc : D.Comm (m + 4) (Hq m) (Bb m false)) :
    Derivable (theory (m + 4)) (drawn [Hq m, Bq m, Hq m, Bq m])
    (drawn [Hq m, Bi m, Hq m, Bi m]) := by
  have m1 := merge_Bb ih true
  have m2 := merge_Bb ih false
  simp only [Bool.not_true, Bool.not_false] at m1 m2
  rw [drawn_two', Bb_true] at m1
  rw [drawn_two', Bb_true] at m2
  unfold D.Comm at hc
  rw [drawn_two', drawn_two'] at hc
  have hinv := inv_Bw ih
  rw [drawn_two'] at hinv
  rw [drawn_four', drawn_four']
  set H := Hq m
  set B := Bq m
  set W := Bb m false
  set I := Bi m
  have e1 : Derivable (theory (m + 4)) (I * H * I * H) ((B * W) * H * (W * B) * H) :=
    dmul (dmul (dmul m2.symm (Derivable.refl _)) m1.symm) (Derivable.refl _)
  have e2 : (B * W) * H * (W * B) * H = B * (W * H) * W * B * H := by simp only [mul_assoc]
  have e3 : Derivable (theory (m + 4)) (B * (W * H) * W * B * H) (B * (H * W) * W * B * H) :=
    dright _ (dright _ (dright _ (dleft _ hc)))
  have e4 : B * (H * W) * W * B * H = B * H * (W * W) * B * H := by simp only [mul_assoc]
  have e5 : Derivable (theory (m + 4)) (B * H * (W * W) * B * H) (B * H * 1 * B * H) :=
    dright _ (dright _ (dleft _ hinv))
  have e6 : B * H * 1 * B * H = B * H * B * H := by rw [mul_one]
  exact ((e1.trans (der_of_eq e2)).trans (e3.trans ((der_of_eq e4).trans
    (e5.trans (der_of_eq e6))))).symm

/-- (353) for the `ZX` and the swap of the wires `1, 2`, from four wires on. -/
theorem comm_zx_sw_1 (hZ : Derivable (theory (m + 4)) (mc (m + 4) .zx [0] (blackOn 1 (m + 4)))
      (drawn [Hq m, Bi m, Hq m, Bi m])) :
    D.Comm (m + 4) (mc (m + 4) .zx [0] (blackOn 1 (m + 4))) (swAt (m + 4) 1) := by
  have hsw := mcSwapBH ih
  have hS : Derivable (theory (m + 4)) (swAt (m + 4) 1 * swAt (m + 4) 1) 1 :=
    swsw (m + 4) 1 (by omega)
  have hH : Derivable (theory (m + 4)) (swAt (m + 4) 1 * Hq m * swAt (m + 4) 1) (Hq m) := by
    have h := hsw 1 (by omega) .hg (Or.inr rfl) [3, 0] (ctlOr (ctlAt 1 true) (ctlOr (ctlAt 2 true) (blackOn 4 (m + 4)))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([3, 0] : List ℕ).map (Net.tau 1) = [3, 0] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have hB : Derivable (theory (m + 4)) (swAt (m + 4) 1 * Bi m * swAt (m + 4) 1) (Bi m) := by
    have h := hsw 1 (by omega) .box (Or.inl rfl) [1] (ctlOr (ctlAt 0 true) (blackOn 3 (m + 4))) rfl (by simp) (by simp)
    rw [conj3] at h
    refine h.trans (der_of_eq ?_) |>.trans (Bi_eq ih).symm
    rw [show ([1] : List ℕ).map (Net.tau 1) = [2] by simp [Net.tau]]
    refine Net.mc_congr _ _ _ (fun j hj => ?_)
    rcases j with _ | _ | _ | _ | j <;> simp [Function.comp, Net.tau, ctlOr, ctlAt, blackOn] <;>
      omega
  have k := via_conj hS (l := [mc (m + 4) .zx [0] (blackOn 1 (m + 4))]) (L := [_])
    (r := [_, _, _, _]) (R := [_, _, _, _])
    (List.Forall₂.cons (Derivable.refl _) List.Forall₂.nil)
    (List.Forall₂.cons hH (List.Forall₂.cons hB (List.Forall₂.cons hH (List.Forall₂.cons hB
      List.Forall₂.nil)))) (by rw [drawn_one']; exact hZ)
  rw [drawn_one'] at k
  exact comm_of_conj hS (k.trans hZ.symm)

end Four

/-! ## The statement -/

/-- (333) at one width, as `N13.eq333` states it. -/
abbrev H333 (n : ℕ) : Prop :=
  Derivable (theory n) (mc n .zx [0] (blackOn 1 n))
    (drawn [mc n .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 n)),
      mc n .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 n)),
      mc n .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 n)),
      mc n .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 n))])

/-- (339) at one width, as `N13.eq339` states it. -/
abbrev H339 (n : ℕ) : Prop :=
  ∀ (x y : ℕ → Bool), DiffOn 3 n x y → ∀ c₁ c₂ c₃ : Bool,
    D.Comm n (mc n .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 n x))))
      (mc n .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 n y)))

/-- (317) at one width, as `N13.eq317` states it. -/
abbrev H317 (n : ℕ) : Prop :=
  ∀ x : ℕ → Bool,
    Derivable (theory n) (drawn [mc n .zx [0] (colOn 1 n x), mc n .xz [0] (colOn 1 n x)]) 1 ∧
    Derivable (theory n) (drawn [mc n .xz [0] (colOn 1 n x), mc n .zx [0] (colOn 1 n x)]) 1

/-- (353) for the `ZX`. -/
theorem comm_zx_sw {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (h333 : H333 N) (h339 : 4 ≤ N → H339 N)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    D.Comm N (mc N .zx [0] (blackOn 1 N)) (swAt N j) := by
  rcases (by omega : 2 ≤ j ∨ j = 1) with hj2 | rfl
  · obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
    exact comm_zx_sw_ge2 k ih j hj2 hjN
  · rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | hN4
    · exact comm_zx_sw_3 ih
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 4 := ⟨N - 4, by omega⟩
      have hc := comm_Hq_Bw ih (fun hd => h339 hN4 _ _ hd true true true)
      exact comm_zx_sw_1 ih ((zx_Hq ih h333).trans (Hq_Bi ih hc))

/-- (353): the multi-controlled `(-1)ᵃ ZX` commutes with the swap of two of
its controls. -/
theorem eq353 {N : ℕ} (hN : 3 ≤ N) (ih : IH N) (h333 : H333 N) (h339 : 4 ≤ N → H339 N)
    (h317 : H317 N) (a : Bool) (j : ℕ) (hj : 1 ≤ j) (hjN : j + 2 ≤ N) :
    Derivable (theory N) (drawn [mc N (Kind.sgnZX a) [0] (blackOn 1 N), swAt N j])
      (drawn [swAt N j, mc N (Kind.sgnZX a) [0] (blackOn 1 N)]) := by
  have hz := comm_zx_sw hN ih h333 h339 j hj hjN
  cases a
  · exact hz
  · have h := h317 (fun _ => true)
    have e : ∀ K, mc N K [0] (colOn 1 N fun _ => true) = mc N K [0] (blackOn 1 N) := fun K =>
      Net.mc_congr _ _ _ (fun i hi => by simp [colOn, blackOn])
    rw [e, e, drawn_two', drawn_two'] at h
    exact N13.Comm.inv hz h.2 h.1

/-- `E.Sym353 N`, from (333), (339) and (317) at every width up to `N`. -/
theorem sym353 {N : ℕ} (ih : IH N)
    (h333 : ∀ n, 3 ≤ n → n ≤ N → H333 n) (h339 : ∀ n, 4 ≤ n → n ≤ N → H339 n)
    (h317 : ∀ n, 3 ≤ n → n ≤ N → H317 n) : E.Sym353 N := by
  intro k hk h3 a j hj hjN
  exact eq353 h3 (ih.mono hk) (h333 _ h3 hk) (fun h4 => h339 _ h4 hk) (h317 _ h3 hk) a j hj hjN

/-- Naturality of every multi-controlled gate for every swap. -/
theorem mcSwapAll {N : ℕ} (ih : IH N)
    (h333 : ∀ n, 3 ≤ n → n ≤ N → H333 n) (h339 : ∀ n, 4 ≤ n → n ≤ N → H339 n)
    (h317 : ∀ n, 3 ≤ n → n ≤ N → H317 n) : E.McSwapAll N :=
  E.mcSwapOf ih (sym353 ih h333 h339 h317)

end QCert.RealCliffordCH.Sec8.D.N13.R347
