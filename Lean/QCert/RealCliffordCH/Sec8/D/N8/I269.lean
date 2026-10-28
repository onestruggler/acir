/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# (269) in the conventions of the interface

From four wires on, (269) is Definition 2.4 of the box: the doubly
controlled `ZX`, `XZ` are the canonical ones at the bottom (`Net.mc_top`,
`Net.mc_canon`), and the inner box `conj τ₀₂ (shift (box _))` is the box on
wire `1` with controls `0, 3, …` (`Net.shift_placeG_id`, `Net.placeG_net`).
On three wires it is Equation (126) (`Small.eq126`), the box `C` being `Z` on
wire `0` there, by one semantic step.
-/
import QCert.RealCliffordCH.Sec8.D.N8.Anchors
import QCert.RealCliffordCH.Sec8.D.Small

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

/-- The box of the interface (`D.Bx`). -/
abbrev BxI (N : ℕ) : Circ N := mc N .box [0] (blackOn 1 N)
/-- The inner box of (269) (`D.Bx1`). -/
abbrev Bx1I (N : ℕ) : Circ N := mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 3 N))

theorem zx_bot : ∀ n : ℕ, mc (n + 3) .zx [0] (blackOn 1 3) = Circuit.pad n (zx 2)
  | 0 => by rw [pad_zero3]; exact mc_canon .zx 2
  | n + 1 => (mc_top (n + 3) .zx [0] _ rfl (by simp) (by simp) (by simp [blackOn])).trans
      (by rw [zx_bot n, padTop_pad3])

theorem xz_bot : ∀ n : ℕ, mc (n + 3) .xz [0] (blackOn 1 3) = Circuit.pad n (xz 2)
  | 0 => by rw [pad_zero3]; exact mc_canon .xz 2
  | n + 1 => (mc_top (n + 3) .xz [0] _ rfl (by simp) (by simp) (by simp [blackOn])).trans
      (by rw [xz_bot n, padTop_pad3])

theorem ctrl_bx1 (n : ℕ) :
    ctrlWires (n + 4) [1] (ctlOr (ctlAt 0 true) (blackOn 3 (n + 4))) =
      0 :: List.range' 3 (n + 1) := by
  have hr : List.range (n + 4) = [0, 1, 2] ++ List.range' 3 (n + 1) := by
    rw [List.range_eq_range', show n + 4 = 3 + (n + 1) by omega, ← List.range'_append_1]
    rfl
  unfold ctrlWires
  rw [hr, List.filter_append]
  have h1 : ([0, 1, 2] : List ℕ).filter (fun j =>
      (ctlOr (ctlAt 0 true) (blackOn 3 (n + 4)) j).isSome && !([1].contains j)) = [0] := by
    rfl
  rw [h1, List.filter_eq_self.2]
  · rfl
  · intro j hj
    rw [List.mem_range'_1] at hj
    have h0 : j ≠ 0 := by omega
    simp [ctlOr, ctlAt, blackOn, h0, show 3 ≤ j ∧ j < n + 4 from ⟨by omega, by omega⟩]
    omega

theorem white_bx1 (n : ℕ) :
    whiteWires (n + 4) [1] (ctlOr (ctlAt 0 true) (blackOn 3 (n + 4))) = [] := by
  unfold whiteWires
  rw [List.filter_eq_nil_iff]
  intro j _
  simp only [ctlOr, ctlAt, blackOn]
  split_ifs <;> simp

theorem bx1_place (n : ℕ) :
    Bx1I (n + 4) = placeG (n + 4) (box (n + 2)) (1 :: 0 :: List.range' 3 (n + 1)) := by
  show mc (n + 4) .box [1] (ctlOr (ctlAt 0 true) (blackOn 3 (n + 4))) = _
  unfold mc
  rw [ctrl_bx1, white_bx1]
  simp only [colourW, List.map_nil, List.nil_append, List.append_nil, drawn_one, List.length_cons,
    List.length_range', List.cons_append]
  rfl

theorem bx1_def (n : ℕ) :
    Derivable (theory (n + 4)) (conj (Circuit.pad (n + 1) (tau02 : Circ 3)) (shift (box (n + 2))))
      (Bx1I (n + 4)) := by
  have h1 := shift_placeG_id (n + 3) (box (n + 2))
  have h2 := placeG_net (N := n + 4) (box (n + 2)) (ps := List.range' 1 (n + 3))
    List.nodup_range' (fun p hp => by rw [List.mem_range'_1] at hp; omega) (by simp)
    [0, 1, 0] (by intro x hx; simp at hx; omega)
  have hps : (List.range' 1 (n + 3)).map (pos ([0, 1, 0] : List ℕ).reverse) =
      1 :: 0 :: List.range' 3 (n + 1) := by
    rw [show n + 3 = 2 + (n + 1) by omega, ← List.range'_append_1]
    simp only [List.map_append]
    rw [List.map_congr_left (l := List.range' (1 + 2) (n + 1)) (g := id) (fun q hq => by
      rw [List.mem_range'_1] at hq
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        pos, List.foldl, Net.tau, id]
      split_ifs <;> omega), List.map_id]
    rfl
  rw [hps] at h2
  rw [bx1_place]
  have ht : Circuit.pad (n + 1) (tau02 : Circ 3) = swW (n + 4) [0, 1, 0] := rfl
  simp only [conj, ht]
  have e : drawn [swW (n + 4) [0, 1, 0], shift (box (n + 2)), swW (n + 4) [0, 1, 0]] =
      swW (n + 4) [0, 1, 0].reverse * shift (box (n + 2)) * swW (n + 4) [0, 1, 0] := by
    simp [drawn, mul_assoc]
  rw [e]
  exact (dctx _ _ h1).trans h2

/-- (269) from four wires on: Definition 2.4. -/
theorem eq269_ge4 (n : ℕ) :
    Derivable (theory (n + 4)) (BxI (n + 4))
      (drawn [mc (n + 4) .zx [0] (blackOn 1 3), Bx1I (n + 4), mc (n + 4) .xz [0] (blackOn 1 3),
        Bx1I (n + 4)]) := by
  have hB : BxI (n + 4) = box (n + 3) := by
    show mc (n + 4) .box [0] (blackOn 1 (n + 4)) = _
    exact mc_canon .box (n + 3)
  have e3 : box (n + 3) = drawn [Circuit.pad (n + 1) zx2,
      conj (Circuit.pad (n + 1) (tau02 : Circ 3)) (shift (box (n + 2))), Circuit.pad (n + 1) xz2,
      conj (Circuit.pad (n + 1) (tau02 : Circ 3)) (shift (box (n + 2)))] := rfl
  have hW : mc (n + 4) .zx [0] (blackOn 1 3) = Circuit.pad (n + 1) zx2 := zx_bot (n + 1)
  have hV : mc (n + 4) .xz [0] (blackOn 1 3) = Circuit.pad (n + 1) xz2 := xz_bot (n + 1)
  rw [hB, e3, hW, hV]
  have hc := bx1_def n
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one] at hc ⊢
  exact dmul hc (dmul (Derivable.refl _) (dmul hc (Derivable.refl _)))


/-! ## Three wires: Equation (126) -/

set_option maxRecDepth 20000 in
theorem l126_eq : l126 = drawn [zx2, (z : Circ 3), xz2, (z : Circ 3)] := by
  rfl

theorem bx1I_3 (ih : IH 3) : Derivable (theory 3) (z : Circ 3) (Bx1I 3) := by
  have h1 : Bx1I 3 = padTop (mc 2 .box [1] (ctlOr (ctlAt 0 true) (blackOn 3 3))) :=
    mc_top 2 .box [1] _ rfl (by simp) (by simp) (by simp [ctlOr, ctlAt, blackOn])
  have h2 : (z : Circ 3) = padTop (Circuit.pad 1 (z : Circ 1)) := by
    rw [padTop_pad1]; rfl
  rw [h1, h2]
  exact sem_step_top ih (Fast.sem_of_fast (by decide +kernel))

theorem eq269_3 (ih : IH 3) :
    Derivable (theory 3) (BxI 3)
      (drawn [mc 3 .zx [0] (blackOn 1 3), Bx1I 3, mc 3 .xz [0] (blackOn 1 3), Bx1I 3]) := by
  have h126 := eq126 0 ih
  rw [pad_zero3, pad_zero3, l126_eq] at h126
  have hB : BxI 3 = r126 := by
    show mc 3 .box [0] (blackOn 1 3) = _
    rw [show mc 3 .box [0] (blackOn 1 3) = box 2 from mc_canon .box 2]
    rfl
  have hW : mc 3 .zx [0] (blackOn 1 3) = zx2 := (zx_bot 0).trans (pad_zero3 _)
  have hV : mc 3 .xz [0] (blackOn 1 3) = xz2 := (xz_bot 0).trans (pad_zero3 _)
  rw [hB, hW, hV]
  have hz := bx1I_3 ih
  refine h126.symm.trans ?_
  simp only [drawn, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, mul_one]
  exact dmul hz (dmul (Derivable.refl _) (dmul hz (Derivable.refl _)))

/-- (269) in the conventions of `MC`, at every width from three on. -/
theorem eq269' (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (BxI N)
      (drawn [mc N .zx [0] (blackOn 1 3), Bx1I N, mc N .xz [0] (blackOn 1 3), Bx1I N]) := by
  rcases (by omega : N = 3 ∨ 4 ≤ N) with rfl | h4
  · exact eq269_3 ih
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 4 := ⟨N - 4, by omega⟩
    exact eq269_ge4 n

end QCert.RealCliffordCH.Sec8.D.N8
