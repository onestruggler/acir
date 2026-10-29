/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (31)

`D((-1)_[a+1](-1)_[c])` and `D((-1)_[a](-1)_[c])` are products of the boxes
`B_k = D((-1)_[k](-1)_[k+1])` (`zzL`), and `R = D((-1)_[a]X_[a,a+1])` is the
rotation on the wire `t` where `G(a)` and `G(a + 1)` differ.

* A box `B_k` with `k ∉ {a - 1, a, a + 1}` passes `R` (`box_rot_comm`): by (346)
  on the same wire, by (347) on two wires, their controls differing on a third
  one (`gray_separated`), as in the paper.
* `B_{a+1}` and `B_{a-1}` have their box on another wire, a control on the
  target of `R`, and otherwise the controls of `R`; such a box conjugates `R`
  into its inverse (`box_inv_rot`): at the canonical position this is the box
  with every control black conjugating `ZX` into `XZ` ((333), (334), (299):
  `D.N15.bx_z1`), coloured by (81), (315) and (356).
* With (355) (`R² = B_a`) and (317), `B_{a+1} R = R B_a B_{a+1}` and
  `B_a B_{a-1} R = R B_{a-1}`, which is the rule for `c > a + 1` and for
  `c < a`.

Every claim was checked numerically (scratch `m31.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule40

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## A box and a rotation commute -/

/-- A decoded box and a decoded rotation commute: on one wire by (346), on two
wires by (347) when their controls differ on another wire. -/
theorem box_rot_comm {M : ℕ} (ih : IH (M + 3)) (γ : Bool) {t t' s s' : ℕ} (ht : t < M + 3)
    (ht' : t' < M + 3)
    (hsep : t ≠ t' → ∃ w, w < M + 3 ∧ w ≠ t ∧ w ≠ t' ∧ s.testBit w ≠ s'.testBit w) :
    D.Comm (M + 3) (mc (M + 3) .box [t'] (ctlOf s' t'))
      (mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t)) := by
  have hK : kindSp (Kind.sgnZX γ) = 1 := by cases γ <;> rfl
  by_cases htt : t = t'
  · subst htt
    have hnd : [t].Nodup := by simp
    have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
    have fB := frame1 ih .box rfl ht s'
    have fR := frame1 ih (Kind.sgnZX γ) hK ht s
    exact via_frame hnd hps (List.Forall₂.cons fB (List.Forall₂.cons fR List.Forall₂.nil))
      (List.Forall₂.cons fR (List.Forall₂.cons fB List.Forall₂.nil))
      (D.eq346 (M + 3) (by omega) ih (pull1 t s') (pull1 t s) γ)
  · have hnd : [t', t].Nodup := by simp [Ne.symm htt]
    have hps : ∀ p ∈ [t', t], p < M + 3 := by simp [ht, ht']
    have f1 := (frame2_one ih .box rfl ht' ht (Ne.symm htt) s').1
    have f2 := (frame2_one ih (Kind.sgnZX γ) hK ht ht' htt s).2
    obtain ⟨w, hw, hwt, hwt', hdiff⟩ := hsep htt
    have hd : DiffOn 2 (M + 3) (pull2 t' t s') (pull2 t' t s) := by
      refine ⟨pos (netOf [t', t]) w, ?_, pos_lt _ (netOf_ok hnd hps) w hw, ?_⟩
      · have h0 : frm [t', t] 0 = t' := frm_getD hnd hps (by simp)
        have h1 : frm [t', t] 1 = t := frm_getD hnd hps (by simp)
        by_contra hlt
        have : pos (netOf [t', t]) w = 0 ∨ pos (netOf [t', t]) w = 1 := by omega
        rcases this with e | e
        · apply hwt'; rw [← frm_pos [t', t] w, e, h0]
        · apply hwt; rw [← frm_pos [t', t] w, e, h1]
      · simp only [pull2, frm_pos, bitOf_eq]
        intro e; apply hdiff
        revert e; cases s.testBit w <;> cases s'.testBit w <;> simp
    exact via_frame hnd hps (List.Forall₂.cons f1 (List.Forall₂.cons f2 List.Forall₂.nil))
      (List.Forall₂.cons f2 (List.Forall₂.cons f1 List.Forall₂.nil))
      (D.eq347 (M + 3) (by omega) ih _ _ hd γ _ _)

/-! ## A box with a control on the target inverts the rotation -/

section Canon

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- The box on wire `1` with controls `c0` on wire `0`, `x` above. -/
abbrev Bc31 (M : ℕ) (c0 : Bool) (x : ℕ → Bool) : Circ (M + 3) :=
  mc (M + 3) .box [1] (ctlOr (ctlAt 0 c0) (colOn 2 (M + 3) x))
/-- The rotation `(-1)^γ ZX` on wire `0` with controls `c1` on wire `1`, `x` above. -/
abbrev Rc31 (M : ℕ) (γ c1 : Bool) (x : ℕ → Bool) : Circ (M + 3) :=
  mc (M + 3) (Kind.sgnZX γ) [0] (ctlOr (ctlAt 1 c1) (colOn 2 (M + 3) x))

/-- All black: `D.N15.bx_z1` moved by the swap of the wires `0, 1`. -/
theorem binv_black (γ : Bool) :
    Derivable (theory (M + 3))
      (Bc31 M true (fun _ => true) * Rc31 M γ true (fun _ => true) * Bc31 M true (fun _ => true))
      (Rc31 M (!γ) true (fun _ => true)) := by
  have hS := swsw (M + 3) 0 (by omega)
  have hB : Derivable (theory (M + 3)) (swAt (M + 3) 0 * D.Bx (M + 3) * swAt (M + 3) 0)
      (Bc31 M true (fun _ => true)) := by
    refine D.N15.sw0_mc ih .box rfl _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn, colOn] <;> omega
  have hZ : ∀ δ : Bool, Derivable (theory (M + 3))
      (swAt (M + 3) 0 * mc (M + 3) (Kind.sgnZX δ) [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) *
        swAt (M + 3) 0) (Rc31 M δ true (fun _ => true)) := by
    intro δ
    refine D.N15.sw0_mc' ih (Kind.sgnZX δ) (by cases δ <;> rfl) _ _ (fun j hj => ?_)
    rcases j with _ | _ | j <;> simp [Net.tau, ctlOr, ctlAt, blackOn, colOn] <;> omega
  -- `B Z B = X`
  have k0 := D.N15.via_conj hS (l := [D.Bx (M + 3), D.N15.Z1 M, D.Bx (M + 3)])
    (L := [Bc31 M true (fun _ => true), Rc31 M false true (fun _ => true), Bc31 M true (fun _ => true)])
    (r := [D.N15.X1 M]) (R := [Rc31 M true true (fun _ => true)])
    (List.Forall₂.cons hB (List.Forall₂.cons (hZ false) (List.Forall₂.cons hB List.Forall₂.nil)))
    (List.Forall₂.cons (hZ true) List.Forall₂.nil)
    (by rw [D.N15.drawn_three', D.N15.drawn_one']; exact D.N15.bx_z1 ih)
  rw [D.N15.drawn_three', D.N15.drawn_one'] at k0
  -- `B B = 1`
  have hBB : Derivable (theory (M + 3)) (Bc31 M true (fun _ => true) * Bc31 M true (fun _ => true)) 1 := by
    have k := D.N15.via_conj hS (l := [D.Bx (M + 3), D.Bx (M + 3)])
      (L := [Bc31 M true (fun _ => true), Bc31 M true (fun _ => true)]) (r := []) (R := [])
      (List.Forall₂.cons hB (List.Forall₂.cons hB List.Forall₂.nil)) List.Forall₂.nil
      (D.eq299 (M + 3) (by omega) ih)
    simpa [drawn] using k
  cases γ
  · exact k0
  · -- `B X B = B (B Z B) B = Z`
    set B := Bc31 M true (fun _ => true)
    refine (dctx B B k0.symm).trans ?_
    have e : B * (B * Rc31 M false true (fun _ => true) * B) * B =
        (B * B) * Rc31 M false true (fun _ => true) * (B * B) := by simp only [mul_assoc]
    rw [e]
    have := dmul (dright (Rc31 M false true (fun _ => true)) hBB) hBB
    simpa using this

/-- The canonical inversion for any colours. -/
theorem binv_c (γ c0 c1 : Bool) (x : ℕ → Bool) :
    Derivable (theory (M + 3)) (Bc31 M c0 x * Rc31 M γ c1 x * Bc31 M c0 x) (Rc31 M (!γ) c1 x) := by
  -- the colours `x` on the wires `2, …`
  have stepA : ∀ δ : Bool, Derivable (theory (M + 3))
      (Bc31 M true x * Rc31 M δ true x * Bc31 M true x) (Rc31 M (!δ) true x) := by
    intro δ
    set ws := (List.range (M + 3)).filter (fun j => decide (2 ≤ j) && !x j) with hws
    have hnd : ws.Nodup := List.nodup_range.filter _
    have hmem : ∀ j ∈ ws, j < M + 3 ∧ 2 ≤ j ∧ x j = false := by
      intro j hj
      obtain ⟨hjN, hp⟩ := List.mem_filter.1 hj
      have hp' : 2 ≤ j ∧ x j = false := by simpa using hp
      exact ⟨List.mem_range.1 hjN, hp'⟩
    have hu := D.xs_inv (M + 3) ws hnd (fun w hw => (hmem w hw).1)
    have colr : ∀ (K : Kind) (tg : List ℕ) (c d : ℕ → Option Bool),
        (∀ j ∈ ws, j ∉ tg ∧ c j = some true) →
        (∀ j < M + 3, d j = if j ∈ ws then some false else c j) →
        Derivable (theory (M + 3)) (drawn (ws.map (xAt (M + 3))) * mc (M + 3) K tg c *
          drawn (ws.map (xAt (M + 3)))) (mc (M + 3) K tg d) := by
      intro K tg c d hc hd
      have h := D.N13.mc_colour (M + 3) K tg c ws hnd
        (fun j hj => ⟨(hmem j hj).1, (hc j hj).1, (hc j hj).2⟩)
      rw [Net.colourW_eq] at h
      exact h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => (hd j hj).symm)))
    have hd : ∀ (i : ℕ) (b : Bool), i < 2 → ∀ j < M + 3,
        ctlOr (ctlAt i b) (colOn 2 (M + 3) x) j =
          if j ∈ ws then some false else ctlOr (ctlAt i b) (colOn 2 (M + 3) fun _ => true) j := by
      intro i b hi j hj
      by_cases hjw : j ∈ ws
      · obtain ⟨_, h2, hx⟩ := hmem j hjw
        rw [if_pos hjw]
        simp [ctlOr, ctlAt, colOn, show j ≠ i by omega, h2, hj, hx]
      · rw [if_neg hjw]
        by_cases h2 : 2 ≤ j
        · have hx : x j = true := by
            by_contra hx
            exact hjw (List.mem_filter.2 ⟨List.mem_range.2 hj, by simp [h2, hx]⟩)
          simp [ctlOr, ctlAt, colOn, show j ≠ i by omega, h2, hj, hx]
        · simp [ctlOr, ctlAt, colOn, h2]
    have hc : ∀ (i : ℕ) (b : Bool) (tg : List ℕ), (∀ t ∈ tg, t < 2) → i < 2 → ∀ j ∈ ws,
        j ∉ tg ∧ ctlOr (ctlAt i b) (colOn 2 (M + 3) fun _ => true) j = some true := by
      intro i b tg htg hi j hj
      obtain ⟨hjN, h2, _⟩ := hmem j hj
      refine ⟨fun h => by have := htg j h; omega, ?_⟩
      simp [ctlOr, ctlAt, colOn, show j ≠ i by omega, h2, hjN]
    have fB := colr .box [1] _ _ (hc 0 true [1] (by simp) (by omega)) (hd 0 true (by omega))
    have fR := colr (Kind.sgnZX δ) [0] _ _ (hc 1 true [0] (by simp) (by omega)) (hd 1 true (by omega))
    have fR' := colr (Kind.sgnZX !δ) [0] _ _ (hc 1 true [0] (by simp) (by omega)) (hd 1 true (by omega))
    have k := D.N15.via_conj hu (l := [Bc31 M true (fun _ => true), Rc31 M δ true (fun _ => true),
        Bc31 M true (fun _ => true)]) (r := [Rc31 M (!δ) true (fun _ => true)])
      (List.Forall₂.cons fB (List.Forall₂.cons fR (List.Forall₂.cons fB List.Forall₂.nil)))
      (List.Forall₂.cons fR' List.Forall₂.nil)
      (by rw [D.N15.drawn_three', D.N15.drawn_one']; exact binv_black ih δ)
    rwa [D.N15.drawn_three', D.N15.drawn_one'] at k
  -- the colour `c1` on wire `1`: `X` there passes the box ((315)) and recolours the rotation
  have stepB : ∀ δ : Bool, Derivable (theory (M + 3))
      (Bc31 M true x * Rc31 M δ c1 x * Bc31 M true x) (Rc31 M (!δ) c1 x) := by
    intro δ
    cases c1
    · have hX := D.xx (M + 3) 1 (by omega)
      have fB : Derivable (theory (M + 3)) (xAt (M + 3) 1 * Bc31 M true x * xAt (M + 3) 1)
          (Bc31 M true x) :=
        D.N15.conj_of_comm hX (xbox (by omega) ih (t := 1) (by omega) _
          (by simp [ctlOr, ctlAt, colOn])
          (fun j hj hj1 => by
            rcases j with _ | _ | j
            · simp [ctlOr, ctlAt]
            · exact absurd rfl hj1
            · simp [ctlOr, ctlAt, colOn, hj])).symm
      have fR : ∀ ε : Bool, Derivable (theory (M + 3)) (xAt (M + 3) 1 * Rc31 M ε true x * xAt (M + 3) 1)
          (Rc31 M ε false x) := by
        intro ε
        have h := D.eq81 (M + 3) (Kind.sgnZX ε) [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) x)) 1 true
          (by omega) (by simp) (by simp [ctlOr, ctlAt])
        rw [D.N15.conj3] at h
        refine h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => ?_)))
        rcases j with _ | _ | j <;> simp [setCtl, ctlOr, ctlAt, colOn]
      have k := D.N15.via_conj hX (l := [Bc31 M true x, Rc31 M δ true x, Bc31 M true x])
        (r := [Rc31 M (!δ) true x])
        (List.Forall₂.cons fB (List.Forall₂.cons (fR δ) (List.Forall₂.cons fB List.Forall₂.nil)))
        (List.Forall₂.cons (fR (!δ)) List.Forall₂.nil)
        (by rw [D.N15.drawn_three', D.N15.drawn_one']; exact stepA δ)
      rwa [D.N15.drawn_three', D.N15.drawn_one'] at k
    · exact stepA δ
  -- the colour `c0` on wire `0`: `X` there recolours the box and inverts the rotation ((356))
  cases c0
  · have hX := D.xx (M + 3) 0 (by omega)
    have fB : Derivable (theory (M + 3)) (xAt (M + 3) 0 * Bc31 M true x * xAt (M + 3) 0)
        (Bc31 M false x) := by
      have h := D.eq81 (M + 3) .box [1] (ctlOr (ctlAt 0 true) (colOn 2 (M + 3) x)) 0 true
        (by omega) (by simp) (by simp [ctlOr, ctlAt])
      rw [D.N15.conj3] at h
      refine h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => ?_)))
      rcases j with _ | _ | j <;> simp [setCtl, ctlOr, ctlAt, colOn]
    have fR : ∀ ε : Bool, Derivable (theory (M + 3)) (xAt (M + 3) 0 * Rc31 M ε c1 x * xAt (M + 3) 0)
        (Rc31 M (!ε) c1 x) := by
      intro ε
      have h := tflip0 (by omega) ih ε (ctlOr (ctlAt 1 c1) (colOn 2 (M + 3) x))
        (by simp [ctlOr, ctlAt, colOn])
        (fun j hj1 hjN => by
          rcases j with _ | _ | j
          · omega
          · simp [ctlOr, ctlAt]
          · simp [ctlOr, ctlAt, colOn, hjN])
      rwa [drawn3] at h
    have k := D.N15.via_conj hX (l := [Bc31 M true x, Rc31 M (!γ) c1 x, Bc31 M true x])
      (r := [Rc31 M (!!γ) c1 x])
      (List.Forall₂.cons fB (List.Forall₂.cons (fR (!γ)) (List.Forall₂.cons fB List.Forall₂.nil)))
      (List.Forall₂.cons (fR (!!γ)) List.Forall₂.nil)
      (by rw [D.N15.drawn_three', D.N15.drawn_one']; exact stepB (!γ))
    rw [D.N15.drawn_three', D.N15.drawn_one'] at k
    simp only [Bool.not_not] at k
    exact k
  · exact stepB γ

end Canon

/-- A box on wire `w` whose controls are those of the rotation on wire `t`,
except on `t` (any colour) and `w` (the box wire), conjugates the rotation into
its inverse. -/
theorem box_inv_rot {M : ℕ} (ih : IH (M + 3)) (γ : Bool) {t w s s' : ℕ} (ht : t < M + 3)
    (hw : w < M + 3) (htw : t ≠ w) (hag : ∀ j, j ≠ t → j ≠ w → bitOf s j = bitOf s' j) :
    Derivable (theory (M + 3))
      (mc (M + 3) .box [w] (ctlOf s' w) * mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t) *
        mc (M + 3) .box [w] (ctlOf s' w))
      (mc (M + 3) (Kind.sgnZX !γ) [t] (ctlOf s t)) := by
  have hK : ∀ ε : Bool, kindSp (Kind.sgnZX ε) = 1 := fun ε => by cases ε <;> rfl
  have hnd : [t, w].Nodup := by simp [htw]
  have hps : ∀ p ∈ [t, w], p < M + 3 := by simp [ht, hw]
  have fR := fun ε => (frame2_one ih (Kind.sgnZX ε) (hK ε) ht hw htw s).1
  have fB := (frame2_one ih .box rfl hw ht (Ne.symm htw) s').2
  have epull : ∀ j < M + 3, ctlOr (ctlAt 0 (decide (bitOf s' t = 1))) (colOn 2 (M + 3) (pull2 t w s')) j =
      ctlOr (ctlAt 0 (decide (bitOf s' t = 1))) (colOn 2 (M + 3) (pull2 t w s)) j := by
    intro j hj
    rcases j with _ | _ | j
    · rfl
    · rfl
    · obtain ⟨hm, _⟩ := D.N15.frm_out' hnd hps (j := j + 2) (by simp) hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      simp [ctlOr, ctlAt, colOn, pull2, hag _ hm.1 hm.2]
  rw [Net.mc_congr (M + 3) .box [1] epull] at fB
  have k := via_frame hnd hps (l := [Bc31 M (decide (bitOf s' t = 1)) (pull2 t w s),
      Rc31 M γ (decide (bitOf s w = 1)) (pull2 t w s), Bc31 M (decide (bitOf s' t = 1)) (pull2 t w s)])
    (r := [Rc31 M (!γ) (decide (bitOf s w = 1)) (pull2 t w s)])
    (List.Forall₂.cons fB (List.Forall₂.cons (fR γ) (List.Forall₂.cons fB List.Forall₂.nil)))
    (List.Forall₂.cons (fR (!γ)) List.Forall₂.nil)
    (by rw [D.N15.drawn_three', D.N15.drawn_one']; exact binv_c ih _ _ _ _)
  rwa [D.N15.drawn_three', D.N15.drawn_one'] at k

/-! ## The rotation squared, and its inverse -/

theorem rot_sq {M : ℕ} (ih : IH (M + 3)) (γ : Bool) {t s : ℕ} (ht : t < M + 3) :
    Derivable (theory (M + 3))
      (mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t) * mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t))
      (mc (M + 3) .box [t] (ctlOf s t)) := by
  have hK : kindSp (Kind.sgnZX γ) = 1 := by cases γ <;> rfl
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have f := fun K hK => frame1 ih K hK ht s
  have := via_frame hnd hps (L := [mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t),
    mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t)]) (R := [mc (M + 3) .box [t] (ctlOf s t)])
    (List.Forall₂.cons (f _ hK) (List.Forall₂.cons (f _ hK) List.Forall₂.nil))
    (List.Forall₂.cons (f .box rfl) List.Forall₂.nil)
    (by rw [drawn_single]; exact D.eq355 (M + 3) (by omega) ih γ (pull1 t s))
  rwa [drawn_single, drawn_two] at this

theorem rot_inv {M : ℕ} (ih : IH (M + 3)) (γ : Bool) {t s : ℕ} (ht : t < M + 3) :
    Derivable (theory (M + 3))
      (mc (M + 3) (Kind.sgnZX !γ) [t] (ctlOf s t) * mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf s t)) 1 := by
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have f := fun K hK => frame1 ih K hK ht s
  have h317 := D.eq317 (M + 3) (by omega) ih (pull1 t s)
  cases γ
  · have := via_frame hnd hps (L := [mc (M + 3) .zx [t] (ctlOf s t),
      mc (M + 3) .xz [t] (ctlOf s t)]) (R := []) (List.Forall₂.cons (f .zx rfl)
      (List.Forall₂.cons (f .xz rfl) List.Forall₂.nil)) List.Forall₂.nil (by simpa [drawn] using h317.1)
    simpa [drawn, Kind.sgnZX] using this
  · have := via_frame hnd hps (L := [mc (M + 3) .xz [t] (ctlOf s t),
      mc (M + 3) .zx [t] (ctlOf s t)]) (R := []) (List.Forall₂.cons (f .xz rfl)
      (List.Forall₂.cons (f .zx rfl) List.Forall₂.nil)) List.Forall₂.nil (by simpa [drawn] using h317.2)
    simpa [drawn, Kind.sgnZX] using this

/-! ## The algebra -/

theorem rule31_up {Q : Type*} [Monoid Q] {r ri ba b1 q : Q} (hrr : r * r = ba) (hiv : ri * r = 1)
    (hba : ba * ba = 1) (hb1 : b1 * b1 = 1) (hinv : b1 * r * b1 = ri) (hc : ba * b1 = b1 * ba)
    (hq : q * r = r * q) : q * b1 * r = r * (q * (b1 * ba)) := by
  have hrba : r * ba = ri := by
    calc r * ba = (ri * r) * r * ba := by rw [hiv, one_mul]
      _ = ri * (r * r) * ba := by simp only [mul_assoc]
      _ = ri * (ba * ba) := by rw [hrr, mul_assoc]
      _ = ri := by rw [hba, mul_one]
  have hstep : b1 * r = r * b1 * ba := by
    calc b1 * r = b1 * r * (b1 * b1) := by rw [hb1, mul_one]
      _ = (b1 * r * b1) * b1 := by simp only [mul_assoc]
      _ = r * ba * b1 := by rw [hinv, hrba]
      _ = r * (ba * b1) := by rw [mul_assoc]
      _ = r * b1 * ba := by rw [hc, mul_assoc]
  calc q * b1 * r = q * (b1 * r) := by rw [mul_assoc]
    _ = q * (r * b1 * ba) := by rw [hstep]
    _ = (q * r) * (b1 * ba) := by simp only [mul_assoc]
    _ = r * (q * (b1 * ba)) := by rw [hq, mul_assoc]

theorem rule31_down {Q : Type*} [Monoid Q] {r ri ba bm q : Q} (hrr : r * r = ba) (hiv : ri * r = 1)
    (hba : ba * ba = 1) (hbm : bm * bm = 1) (hinv : bm * r * bm = ri) (hcr : ba * r = r * ba)
    (hq : q * r = r * q) : ba * bm * q * r = r * (bm * q) := by
  have hrba : r * ba = ri := by
    calc r * ba = (ri * r) * r * ba := by rw [hiv, one_mul]
      _ = ri * (r * r) * ba := by simp only [mul_assoc]
      _ = ri * (ba * ba) := by rw [hrr, mul_assoc]
      _ = ri := by rw [hba, mul_one]
  have hstep : ba * bm * r = r * bm := by
    calc ba * bm * r = ba * (bm * r * bm) * bm := by
          simp only [mul_assoc]; rw [hbm, mul_one]
      _ = ba * (r * ba) * bm := by rw [hinv, hrba]
      _ = (ba * r) * ba * bm := by simp only [mul_assoc]
      _ = r * (ba * ba) * bm := by rw [hcr]; simp only [mul_assoc]
      _ = r * bm := by rw [hba, mul_one]
  calc ba * bm * q * r = ba * bm * (q * r) := by rw [mul_assoc]
    _ = ba * bm * (r * q) := by rw [hq]
    _ = (ba * bm * r) * q := by simp only [mul_assoc]
    _ = r * (bm * q) := by rw [hstep, mul_assoc]

/-! ## The rule -/

theorem dZZ1_eq {M k : ℕ} :
    dZZ1 (M + 3) k = mc (M + 3) .box [tOf (M + 3) k] (ctlOf (gray k) (tOf (M + 3) k)) :=
  dZZ1_mc (M + 2) k

theorem agree_succ {n a : ℕ} (ha : a + 1 < 2 ^ n) :
    ∀ j, j ≠ tOf n a → bitOf (gray a) j = bitOf (gray (a + 1)) j := by
  intro j hj
  rw [bitOf_eq_bitOf, gray_succ_tOf ha, testBit_xor_pow_ne hj]

/-- (31) decodes to (346), (347), the inversion `box_inv_rot`, (355) and (317). -/
theorem dec31 {M : ℕ} (ih : IH (M + 3)) (a c : ℕ) (ha : a + 1 < 2 ^ (M + 3)) (hc : c < 2 ^ (M + 3))
    (hca : c ≠ a) (hca1 : c ≠ a + 1) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Zz (M + 3) (a + 1) c, Zx (M + 3) a a (a + 1)]))
      (decW (M + 3) (wordOf [Zx (M + 3) a a (a + 1), Zz (M + 3) a c])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one, dec_Zx_lo ha,
    dec_Zz (by omega : a + 1 < 2 ^ (M + 3)) hc, dec_Zz (by omega : a < 2 ^ (M + 3)) hc]
  rw [dZX1_mc (M + 2)]
  obtain ⟨γ, hγ⟩ := kindZX_sgn (k := M + 2) (a := a) 0
  rw [hγ]
  have ht : tOf (M + 3) a < M + 3 := tOf_lt a (by omega)
  set t := tOf (M + 3) a with htdef
  set R := mc (M + 3) (Kind.sgnZX γ) [t] (ctlOf (gray a) t) with hR
  set Ri := mc (M + 3) (Kind.sgnZX !γ) [t] (ctlOf (gray a) t) with hRi
  set Ba := mc (M + 3) .box [t] (ctlOf (gray a) t) with hBa
  have hrr := rot_sq ih γ (s := gray a) ht
  have hiv := rot_inv ih γ (s := gray a) ht
  have hba : Derivable (theory (M + 3)) (Ba * Ba) 1 := by
    have := box_inv ih (t := t) (s := gray a) ht; rwa [drawn_two] at this
  have bInv : ∀ k w, w < M + 3 →
      Derivable (theory (M + 3)) (mc (M + 3) .box [w] (ctlOf k w) * mc (M + 3) .box [w] (ctlOf k w)) 1 :=
    fun k w hw => by have := box_inv ih (t := w) (s := k) hw; rwa [drawn_two] at this
  -- far boxes pass `R`
  have far : ∀ k, (a + 1 < k ∨ k + 1 < a) → k + 1 < 2 ^ (M + 3) →
      D.Comm (M + 3) (dZZ1 (M + 3) k) R := by
    intro k hk hk1
    rw [dZZ1_eq]
    refine box_rot_comm ih γ ht (tOf_lt k (by omega)) (fun htt => ?_)
    rcases hk with hk | hk
    · obtain ⟨w, hw, h1, h2, h3⟩ := gray_separated (n := M + 3) hk hk1 htt
      exact ⟨w, hw, h1, h2, h3⟩
    · obtain ⟨w, hw, h1, h2, h3⟩ := gray_separated (n := M + 3) hk ha (Ne.symm htt)
      exact ⟨w, hw, h2, h1, fun e => h3 e.symm⟩
  have farL : ∀ (l : List ℕ), (∀ k ∈ l, (a + 1 < k ∨ k + 1 < a) ∧ k + 1 < 2 ^ (M + 3)) →
      Derivable (theory (M + 3)) (drawn (l.map (dZZ1 (M + 3))) * R) (R * drawn (l.map (dZZ1 (M + 3)))) := by
    intro l hl
    have h := D.N13.comm_drawn_left (c := R) (l.map (dZZ1 (M + 3))) (fun g hg => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
      exact far k (hl k hk).1 (hl k hk).2)
    unfold D.Comm at h
    rw [drawn_two, drawn_two] at h
    exact h.symm
  have zzL_map : ∀ x y, zzL (M + 3) x y = ((List.range (y - x)).map (x + ·)).map (dZZ1 (M + 3)) := by
    intro x y; simp [zzL, List.map_map, Function.comp_def]
  rcases (by omega : a + 1 < c ∨ c < a) with hup | hdown
  · -- `c > a + 1`
    have ha2 : a + 2 < 2 ^ (M + 3) := by omega
    have hw : tOf (M + 3) (a + 1) < M + 3 := tOf_lt (a + 1) (by omega)
    have htw : t ≠ tOf (M + 3) (a + 1) := tOf_succ_ne ha2
    set B1 := mc (M + 3) .box [tOf (M + 3) (a + 1)] (ctlOf (gray (a + 1)) (tOf (M + 3) (a + 1))) with hB1
    have hinv := box_inv_rot ih γ ht hw htw (s := gray a) (s' := gray (a + 1))
      (fun j hj _ => agree_succ ha j hj)
    have hc1 : Derivable (theory (M + 3)) (Ba * B1) (B1 * Ba) := by
      have h := boxes_comm ih (t := t) (t' := tOf (M + 3) (a + 1)) (s := gray a) (s' := gray (a + 1))
        ht hw
      unfold D.Comm at h; rw [drawn_two, drawn_two] at h; exact h.symm
    rw [dZZ_zzL (n := M + 3) (a := a + 1) (b := c) (by omega), dZZ_zzL (n := M + 3) (a := a) (b := c) (by omega),
      zzL_split (n := M + 3) (a := a) (b := a + 1) (c := c) (by omega) (by omega),
      zzL_split (n := M + 3) (a := a + 1) (b := a + 2) (c := c) (by omega) (by omega)]
    have e1 : zzL (M + 3) a (a + 1) = [Ba] := by
      simp [zzL, dZZ1_eq, hBa, htdef]
    have e2 : zzL (M + 3) (a + 1) (a + 2) = [B1] := by
      simp [zzL, dZZ1_eq, hB1]
    simp only [e1, e2, drawn_append, drawn_single]
    have hq : Derivable (theory (M + 3)) (drawn (zzL (M + 3) (a + 2) c) * R)
        (R * drawn (zzL (M + 3) (a + 2) c)) := by
      rw [zzL_map]
      refine farL _ (fun k hk => ?_)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      have := List.mem_range.1 hi
      exact ⟨Or.inl (by omega), by omega⟩
    have key := rule31_up (Q := (conGen (theory (M + 3))).Quotient) (r := (R : (conGen (theory (M + 3))).Quotient))
      (ri := Ri) (ba := Ba) (b1 := B1) (q := drawn (zzL (M + 3) (a + 2) c))
      (by rw [← Con.coe_mul]; exact (Con.eq _).2 hrr)
      (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hiv)
      (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hba)
      (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 (bInv _ _ hw))
      (by simp only [← Con.coe_mul]; exact (Con.eq _).2 hinv)
      (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hc1)
      (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hq)
    apply (Con.eq _).1
    simp only [Con.coe_mul, mul_assoc] at key ⊢
    exact key
  · -- `c < a`
    have ha1 : 1 ≤ a := by omega
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hw : tOf (M + 3) a' < M + 3 := tOf_lt a' (by omega)
    have htw : tOf (M + 3) a' ≠ t := tOf_succ_ne (by omega)
    set Bm := mc (M + 3) .box [tOf (M + 3) a'] (ctlOf (gray a') (tOf (M + 3) a')) with hBm
    have hinv := box_inv_rot ih γ ht hw (Ne.symm htw) (s := gray (a' + 1)) (s' := gray a')
      (fun j _ hj => (agree_succ (by omega) j hj).symm)
    have hcr : Derivable (theory (M + 3)) (Ba * R) (R * Ba) := by
      have h := box_rot_comm ih γ (t := t) (t' := t) (s := gray (a' + 1)) (s' := gray (a' + 1)) ht ht
        (fun h => absurd rfl h)
      unfold D.Comm at h; rw [drawn_two, drawn_two] at h; exact h.symm
    rw [dZZ_zzL' (n := M + 3) (a := a' + 1 + 1) (b := c) (by omega),
      dZZ_zzL' (n := M + 3) (a := a' + 1) (b := c) (by omega),
      zzL_split (n := M + 3) (a := c) (b := a') (c := a' + 1 + 1) (by omega) (by omega),
      zzL_split (n := M + 3) (a := c) (b := a') (c := a' + 1) (by omega) (by omega),
      zzL_split (n := M + 3) (a := a') (b := a' + 1) (c := a' + 1 + 1) (by omega) (by omega)]
    have e1 : zzL (M + 3) a' (a' + 1) = [Bm] := by simp [zzL, dZZ1_eq, hBm]
    have e2 : zzL (M + 3) (a' + 1) (a' + 1 + 1) = [Ba] := by simp [zzL, dZZ1_eq, hBa, htdef]
    simp only [e1, e2, drawn_append, drawn_single]
    have hq : Derivable (theory (M + 3)) (drawn (zzL (M + 3) c a') * R)
        (R * drawn (zzL (M + 3) c a')) := by
      rw [zzL_map]
      refine farL _ (fun k hk => ?_)
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      have := List.mem_range.1 hi
      exact ⟨Or.inr (by omega), by omega⟩
    have key := rule31_down (Q := (conGen (theory (M + 3))).Quotient)
      (r := (R : (conGen (theory (M + 3))).Quotient)) (ri := Ri) (ba := Ba) (bm := Bm)
      (q := drawn (zzL (M + 3) c a'))
      (by rw [← Con.coe_mul]; exact (Con.eq _).2 hrr)
      (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hiv)
      (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hba)
      (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 (bInv _ _ hw))
      (by simp only [← Con.coe_mul]; exact (Con.eq _).2 hinv)
      (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hcr)
      (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hq)
    apply (Con.eq _).1
    simp only [Con.coe_mul, mul_assoc] at key ⊢
    exact key

end QCert.RealCliffordCH.Sec8.E
