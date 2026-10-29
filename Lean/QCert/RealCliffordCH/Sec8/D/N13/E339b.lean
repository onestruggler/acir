/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (339) from six wires on, by semantic separation

The frame is `E339a`'s (`sep_reduce` at wire `3`, then the swap of the
wires `2, 3`): `A` is the box on wire `0` coloured by `xE c₁ c₂ x` (black on
wire `2`), `B = BE` the multi-controlled `H` on the wires `1, 3` (white on
wire `2`).  Both are written as products of pieces, and every piece of one
commutes with every piece of the other.

* `A`: the swap of the wires `3, 4` (`box_relabel`, `j = 3`) and (320)/(321)
  (`expX`): its rotations `S₃ r S₃` live on the wires `0, 1, 2, 4`, its
  remainder `Ar` (`S₃ · boxN · S₃`) is idle on wire `4`.
* `B`: `expBE`, the swap of the wires `1, 2` on the inner box, and
  (320)/(321): its pieces are conjugated by `uL … uL'` (`M` then `S₁`), its
  rotations white on wire `2`; its remainder is, by `remB`, the box on wire
  `1` idle on wire `3`.

The four kinds of pairs:
* rotation against rotation: `E339s.commRR_s` (completeness on five wires);
* `Ar` against a rotation of `B`: `E339s.commAr_s`, coloured;
* a rotation of `A` against the remainder of `B`: conjugated by `S₃`, both
  avoid wire `4` and are separated on wire `2` (`commRrem`: `Sep.sep_sem`
  and a semantic step without wire `4`);
* the two remainders (idle on wire `4`, resp. `3`): each is the product of
  its two colourings of the idle wire by the merge (309), and the four
  products are (336) (`commRemRem`).

No window is decided here.  Memory (2026-10-29): 44 s, peak 0.49 GB anonymous
(3.3 GB resident with the mapped imports).  `comm339_ge6` is (339) from six
wires on; it replaces the predecessor's `E339`, `E339r1`–`E339r3`, whose
five-wire windows could not be built.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E339s

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8 Sep

/-! ## Colourings -/

/-- The colours of the box of `A` after the swap of the wires `3, 4`. -/
def xF (c₁ c₂ : Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₂ else if i = 2 then true else if i = 3 then x 4 else
    if i = 4 then c₁ else x i

/-- The colours of the box inside `B` after the swap of the wires `1, 2`. -/
def zS (c₃ : Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₃ else if i = 2 then false else if i = 3 then true else y i

/-- The colours of the remainder of `A` (wire `4` idle). -/
def xA (c₁ c₂ : Bool) (x : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₂ else if i = 2 then true else if i = 3 then c₁ else x i

/-- The remainder of `A` with wire `4` coloured `b`, from wire `2` on. -/
def xA4 (c₁ : Bool) (x : ℕ → Bool) (b : Bool) : ℕ → Bool :=
  fun i => if i = 2 then true else if i = 3 then c₁ else if i = 4 then b else x i

/-- The colours of the remainder of `B` (wire `3` idle). -/
def yB (c₃ : Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i => if i = 1 then c₃ else if i = 2 then false else y i

/-- The remainder of `B` with wire `3` coloured `b`, from wire `2` on. -/
def yB3 (y : ℕ → Bool) (b : Bool) : ℕ → Bool :=
  fun i => if i = 2 then false else if i = 3 then b else y i

/-- Pointwise equality of control functions on the wires `0, …, 4` and above. -/
macro "ctl_case9" : tactic => `(tactic| (intro i hi; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨
  i = 3 ∨ i = 4 ∨ 5 ≤ i) with h | h | h | h | h | h5 <;> (try subst h) <;>
  simp only [colOn, ctlOr, ctlAt, yH, yS, xE, xF, zS, xA, xA4, yB, yB3, ctlX, setCtl,
    Net.tau, Function.comp] <;> (try split_ifs) <;>
  first | rfl | (exfalso; omega) | (simp [List.lookup]; done) | omega))

/-! ## Step 1: `A` as the product of its pieces -/

/-- `A`, the box of the frame, between the swaps of the wires `3, 4`. -/
theorem relA (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ : Bool) :
    Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x)))
      (swAt (m + 6) 3 * mc (m + 6) .box [0] (colOn 1 (m + 6) (xF c₁ c₂ x)) * swAt (m + 6) 3) := by
  have h := box_relabel (m + 6) (by omega) ih 0 (by omega) (colOn 1 (m + 6) (xF c₁ c₂ x))
    (fun i hi hi0 => by simp only [colOn]; split_ifs <;> simp <;> omega) 3 (by omega)
    (by omega) (by omega)
  exact (h.trans (der_of_eq (mc_congr _ _ _ (by ctl_case9)))).symm

theorem pcs4_xF (c₁ c₂ : Bool) (x : ℕ → Bool) :
    pcs4 (xF c₁ c₂ x 1) (xF c₁ c₂ x 2) (xF c₁ c₂ x 3) = pcs4 c₂ true (x 4) := by
  simp [xF]

/-- The pieces of `A`. -/
abbrev piecesA (m : ℕ) (x : ℕ → Bool) (c₁ c₂ : Bool) : List (Circ (m + 6)) :=
  ((pcs4 c₂ true (x 4)).map (cX 4 (m + 6) (xF c₁ c₂ x))).map
    (fun a => swAt (m + 6) 3 * a * swAt (m + 6) 3)

theorem expA9 (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ : Bool) :
    Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x)))
      (drawn (piecesA m x c₁ c₂)) := by
  have hs := swsw (m + 6) 3 (by omega)
  have ex := expX (m + 6) (by omega) ih (xF c₁ c₂ x)
  rw [pcs4_xF] at ex
  exact (relA m ih x c₁ c₂).trans ((dright _ (dleft _ ex)).trans (conj_drawn hs hs _))

/-! ## Step 2: `B` as the product of its pieces -/

/-- The inner box of `B`, between the swaps of the wires `1, 2`. -/
theorem relB (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c₃ : Bool) :
    Derivable (theory (m + 6)) (mc (m + 6) .box [0] (colOn 1 (m + 6) (yS c₃ y)))
      (swAt (m + 6) 1 * mc (m + 6) .box [0] (colOn 1 (m + 6) (zS c₃ y)) * swAt (m + 6) 1) := by
  have h := box_relabel (m + 6) (by omega) ih 0 (by omega) (colOn 1 (m + 6) (zS c₃ y))
    (fun i hi hi0 => by simp only [colOn]; split_ifs <;> simp <;> omega) 1 (by omega)
    (by omega) (by omega)
  exact (h.trans (der_of_eq (mc_congr _ _ _ (by ctl_case9)))).symm

theorem wc_uL' (N : ℕ) : wc 4 N uL' = wc 4 N mL * swAt N 1 := by
  simp only [uL', wc_append, wc_one', circ_S]

theorem wc_uL (N : ℕ) : wc 4 N uL = swAt N 1 * wc 4 N mL' := by
  simp only [uL, wc_append, wc_one', circ_S]

/-- `uL` and `uL'` are inverse, as derivations. -/
theorem uu_inv (m : ℕ) (ih : IH (m + 6)) :
    Derivable (theory (m + 6)) (wc 4 (m + 6) uL * wc 4 (m + 6) uL') 1 ∧
    Derivable (theory (m + 6)) (wc 4 (m + 6) uL' * wc 4 (m + 6) uL) 1 := by
  have hMM := MM_inv m ih
  have hs := swsw (m + 6) 1 (by omega)
  rw [wc_uL, wc_uL']
  constructor
  · have e : swAt (m + 6) 1 * wc 4 (m + 6) mL' * (wc 4 (m + 6) mL * swAt (m + 6) 1) =
        swAt (m + 6) 1 * (wc 4 (m + 6) mL' * wc 4 (m + 6) mL) * swAt (m + 6) 1 := by
      simp only [mul_assoc]
    rw [e]
    refine (dctx _ _ hMM.1).trans ?_
    simpa only [mul_one] using hs
  · have e : wc 4 (m + 6) mL * swAt (m + 6) 1 * (swAt (m + 6) 1 * wc 4 (m + 6) mL') =
        wc 4 (m + 6) mL * (swAt (m + 6) 1 * swAt (m + 6) 1) * wc 4 (m + 6) mL' := by
      simp only [mul_assoc]
    rw [e]
    refine (dctx _ _ hs).trans ?_
    simpa only [mul_one] using hMM.2

theorem pcs4_zS (c₃ : Bool) (y : ℕ → Bool) :
    pcs4 (zS c₃ y 1) (zS c₃ y 2) (zS c₃ y 3) = pcs4 c₃ false true := by
  simp [zS]

/-- The pieces of `B`. -/
abbrev piecesB (m : ℕ) (y : ℕ → Bool) (c₃ : Bool) : List (Circ (m + 6)) :=
  ((pcs4 c₃ false true).map (cX 4 (m + 6) (zS c₃ y))).map
    (fun a => wc 4 (m + 6) uL' * a * wc 4 (m + 6) uL)

theorem expB9 (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c₃ : Bool) :
    Derivable (theory (m + 6)) (BE (m + 6) c₃ y) (drawn (piecesB m y c₃)) := by
  have hu := uu_inv m ih
  have ex := expX (m + 6) (by omega) ih (zS c₃ y)
  rw [pcs4_zS] at ex
  have k1 := (relB m ih y c₃).trans (dright _ (dleft _ ex))
  have k2 := (expBE m ih c₃ y).trans (dright _ (dleft _ k1))
  have e : wc 4 (m + 6) mL * (swAt (m + 6) 1 *
      wcX 4 (m + 6) (zS c₃ y) (pcs4 c₃ false true) * swAt (m + 6) 1) * wc 4 (m + 6) mL' =
      wc 4 (m + 6) uL' * wcX 4 (m + 6) (zS c₃ y) (pcs4 c₃ false true) * wc 4 (m + 6) uL := by
    rw [wc_uL, wc_uL']; simp only [mul_assoc]
  rw [e] at k2
  exact k2.trans (conj_drawn hu.1 hu.2 _)

/-! ## The remainders -/

/-- The remainder of `A`, conjugated by the swap of the wires `3, 4`: `Ar`
coloured by `x` above wire `4`. -/
theorem remA (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ : Bool) :
    Derivable (theory (m + 6))
      (swAt (m + 6) 3 * cX 4 (m + 6) (xF c₁ c₂ x) (P3' c₂ true) * swAt (m + 6) 3)
      (cX 5 (m + 6) x (Ar c₁ c₂)) := by
  rw [P3'_cX]
  have e : cX 5 (m + 6) x (Ar c₁ c₂) =
      mc (m + 6) .box [0] (ctlX 5 [(1, c₂), (2, true), (3, c₁)] x) := rfl
  rw [e]
  exact swBH ih 3 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 2 true) (colOn 4 (m + 6) (xF c₁ c₂ x))))
    (ctlX 5 [(1, c₂), (2, true), (3, c₁)] x) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case9)

/-- The remainder of `B`, conjugated back: the box on wire `1`, idle on wire `3`. -/
theorem remB' (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c₃ : Bool) :
    Derivable (theory (m + 6))
      (wc 4 (m + 6) uL' * cX 4 (m + 6) (zS c₃ y) (P3' c₃ false) * wc 4 (m + 6) uL)
      (swAt (m + 6) 0 * boxN (m + 6) y c₃ false * swAt (m + 6) 0) := by
  rw [P3'_cX, wc_uL, wc_uL']
  have h1 := swBH ih 1 (by omega) .box (Or.inl rfl) [0] [0]
    (ctlOr (ctlAt 1 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) (zS c₃ y))))
    (ctlOr (ctlAt 1 false) (ctlOr (ctlAt 2 c₃) (colOn 4 (m + 6) (yS c₃ y)))) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case9)
  have e : wc 4 (m + 6) mL * swAt (m + 6) 1 * boxN (m + 6) (zS c₃ y) c₃ false *
      (swAt (m + 6) 1 * wc 4 (m + 6) mL') =
      wc 4 (m + 6) mL * (swAt (m + 6) 1 * boxN (m + 6) (zS c₃ y) c₃ false * swAt (m + 6) 1) *
        wc 4 (m + 6) mL' := by simp only [mul_assoc]
  rw [e]
  exact (dctx _ _ h1).trans (remB m ih c₃ y)

/-! ## Step 3: a rotation of `A` against the remainder of `B` -/

/-- The remainder of `B` conjugated by the swap of the wires `3, 4`: idle on
wire `4`, its control on wire `3` of colour `b`. -/
def Yl (c₃ b : Bool) : Lt := .g .box [1] [(0, c₃), (2, false), (3, b)] true

theorem Yl_drop4 : ∀ c₃ b : Bool,
    (Yl c₃ b).ok 5 = true ∧ (Yl c₃ b).avoids 4 = true ∧ (Yl c₃ b).drop 4 = Yl c₃ b := by
  decide

/-- A rotation of `A` (black on wire `2`) passes the box `Yl` (white on wire
`2`): both avoid wire `4`. -/
theorem commRY (m : ℕ) (ih : IH (m + 6)) {b1 b3 : Bool} {r : Lt} (hr : r ∈ rots b1 true b3)
    (c₃ b : Bool) :
    Derivable (theory (m + 6)) (wc 5 (m + 6) ([r] ++ [Yl c₃ b]))
      (wc 5 (m + 6) ([Yl c₃ b] ++ [r])) := by
  have hr4 := rots_drop4 _ _ _ r hr
  have hY := Yl_drop4 c₃ b
  have mem : ∀ x ∈ [r] ++ [Yl c₃ b], x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x := by
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hr4
    · exact hY
  have mem' : ∀ x ∈ [Yl c₃ b] ++ [r], x.ok 5 = true ∧ x.avoids 4 = true ∧ x.drop 4 = x :=
    fun x hx => mem x (by simp only [List.mem_append] at hx ⊢; tauto)
  have e1 : ([r] ++ [Yl c₃ b]).map (Lt.drop 4) = [r] ++ [Yl c₃ b] := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem x hx).2.2), List.map_id]
  have e2 : ([Yl c₃ b] ++ [r]).map (Lt.drop 4) = [Yl c₃ b] ++ [r] := by
    rw [List.map_congr_left (g := id) (fun x hx => (mem' x hx).2.2), List.map_id]
  have tR : Triv 2 0 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) [r])) := by
    rw [wc_one', ← rots_rebase hr]
    simpa using triv_rots (m + 1 + 4) (by omega) b1 true b3 r hr
  have tY : Triv 2 1 (opsQ.eval (m + 1 + 4) (wc 4 (m + 1 + 4) [Yl c₃ b])) := by
    have := triv_g (K := 4) (N := m + 1 + 4) (by omega) .box [1] [(0, c₃), (2, false), (3, b)]
      true rfl (p := 2) (by omega) (by decide) (b := false) rfl
    simpa [wc, drawn, Yl] using this
  have hsem := sep_sem (K := 4) (M := m + 1 + 4) (by decide : (0 : Fin 2) ≠ 1) tR tY
  rw [← e1, ← e2] at hsem
  exact SE.Frame.window (frame 4) (m + 1) ih (q := 4) le_rfl
    (fun x hx => ⟨(mem x hx).1, (mem x hx).2.1⟩) (fun x hx => ⟨(mem' x hx).1, (mem' x hx).2.1⟩)
    hsem

/-- A rotation of `A`, conjugated by the swap of the wires `3, 4`, passes the
remainder of `B`. -/
theorem commRrem (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c₃ : Bool) {b1 b3 : Bool} {r : Lt}
    (hr : r ∈ rots b1 true b3) :
    Comm (m + 6) (swAt (m + 6) 3 * r.circ 4 (m + 6) * swAt (m + 6) 3)
      (swAt (m + 6) 0 * boxN (m + 6) y c₃ false * swAt (m + 6) 0) := by
  -- the remainder as the box on wire `1`
  have h0 : Derivable (theory (m + 6)) (swAt (m + 6) 0 * boxN (m + 6) y c₃ false * swAt (m + 6) 0)
      (mc (m + 6) .box [1] (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y)))) :=
    mc_s0 (m + 6) (by omega) _ 0 (by omega) _ _ (by decide) (by ctl_case9)
  -- conjugated by the swap of the wires `3, 4`
  have h3 := swBH ih 3 (by omega) .box (Or.inl rfl) [1] [1]
    (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y)))
    (ctlX 5 [(0, c₃), (2, false), (3, y 4)] y) rfl (by decide)
    (by intro t ht; simp at ht; omega) rfl (by ctl_case9)
  have eY : cX 5 (m + 6) y (Yl c₃ (y 4)) =
      mc (m + 6) .box [1] (ctlX 5 [(0, c₃), (2, false), (3, y 4)] y) := rfl
  -- the commutation without wire `4`, coloured by `y`
  have d := commRY m ih hr c₃ (y 4)
  have hr4 := rots_drop4 _ _ _ r hr
  have hl : ∀ g ∈ [r] ++ [Yl c₃ (y 4)], g.ok 5 = true := by
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact hr4.1
    · exact (Yl_drop4 c₃ (y 4)).1
  have hr' : ∀ g ∈ [Yl c₃ (y 4)] ++ [r], g.ok 5 = true :=
    fun g hg => hl g (by simp only [List.mem_append] at hg ⊢; tauto)
  have hc := colour_wc (K := 5) (N := m + 6) (by omega) y hl hr' d
  have hc' : Comm (m + 6) (r.circ 4 (m + 6)) (cX 5 (m + 6) y (Yl c₃ (y 4))) := by
    have e : cX 5 (m + 6) y r = r.circ 4 (m + 6) := by rw [rots_cX hr, rots_rebase hr]
    unfold Comm
    simpa only [wcX, List.singleton_append, List.map_cons, List.map_nil, e] using hc
  rw [eY] at hc'
  have hs := swsw (m + 6) 3 (by omega)
  have k := Comm.conj hc' hs
  refine Comm.congr (Derivable.refl _) ?_ k
  exact (conj_back hs h3).trans h0.symm

/-! ## Step 4: the two remainders -/

/-- The merge (309) on wire `w` of a box on wire `0`. -/
theorem merge2 (m : ℕ) (ih : IH (m + 6)) (z : ℕ → Bool) (w : ℕ) (hw : 1 ≤ w) (hwN : w < m + 6) :
    Derivable (theory (m + 6)) (mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) z) w none))
      (drawn [mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) z) w (some true)),
        mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) z) w (some false))]) :=
  (eq309 (m + 6) (by omega) ih z w hw hwN true).symm

/-- The coloured box `a` of the merge of the remainder of `A` on wire `4`. -/
abbrev aM (m : ℕ) (x : ℕ → Bool) (c₁ c₂ b : Bool) : Circ (m + 6) :=
  mc (m + 6) .box [0] (ctlOr (ctlAt 1 c₂) (colOn 2 (m + 6) (xA4 c₁ x b)))

/-- The coloured box of the merge of the remainder of `B` on wire `3`. -/
abbrev bM (m : ℕ) (y : ℕ → Bool) (c₃ b : Bool) : Circ (m + 6) :=
  mc (m + 6) .box [1] (ctlOr (ctlAt 0 c₃) (colOn 2 (m + 6) (yB3 y b)))

theorem drawn2_congr {N : ℕ} {p q p' q' : Circ N} (hp : Derivable (theory N) p p')
    (hq : Derivable (theory N) q q') : Derivable (theory N) (drawn [p, q]) (drawn [p', q']) := by
  rw [drawn_two, drawn_two]; exact dmul hq hp

theorem eA_ctl (m : ℕ) (x : ℕ → Bool) (c₁ c₂ : Bool) :
    cX 5 (m + 6) x (Ar c₁ c₂) = mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) (xA c₁ c₂ x)) 4 none) := by
  have e0 : cX 5 (m + 6) x (Ar c₁ c₂) =
      mc (m + 6) .box [0] (ctlX 5 [(1, c₂), (2, true), (3, c₁)] x) := rfl
  rw [e0]
  exact mc_congr _ _ _ (by ctl_case9)

theorem aM_eq (m : ℕ) (x : ℕ → Bool) (c₁ c₂ b : Bool) :
    mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) (xA c₁ c₂ x)) 4 (some b)) = aM m x c₁ c₂ b :=
  mc_congr _ _ _ (by ctl_case9)

theorem splitA (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ : Bool) :
    Derivable (theory (m + 6)) (cX 5 (m + 6) x (Ar c₁ c₂))
      (drawn [aM m x c₁ c₂ true, aM m x c₁ c₂ false]) := by
  rw [eA_ctl, ← aM_eq m x c₁ c₂ true, ← aM_eq m x c₁ c₂ false]
  exact merge2 m ih (xA c₁ c₂ x) 4 (by omega) (by omega)

theorem eB_ctl (m : ℕ) (y : ℕ → Bool) (c₃ : Bool) :
    boxN (m + 6) y c₃ false = mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) (yB c₃ y)) 3 none) :=
  mc_congr _ _ _ (by ctl_case9)

theorem bM_der (m : ℕ) (y : ℕ → Bool) (c₃ b : Bool) :
    Derivable (theory (m + 6))
      (swAt (m + 6) 0 * mc (m + 6) .box [0] (setCtl (colOn 1 (m + 6) (yB c₃ y)) 3 (some b)) *
        swAt (m + 6) 0) (bM m y c₃ b) :=
  mc_s0 (m + 6) (by omega) .box 0 (by omega) _ _ (by decide) (by ctl_case9)

theorem splitB (m : ℕ) (ih : IH (m + 6)) (y : ℕ → Bool) (c₃ : Bool) :
    Derivable (theory (m + 6)) (swAt (m + 6) 0 * boxN (m + 6) y c₃ false * swAt (m + 6) 0)
      (drawn [bM m y c₃ true, bM m y c₃ false]) := by
  have hs := swsw (m + 6) 0 (by omega)
  rw [eB_ctl]
  refine (dright _ (dleft _ (merge2 m ih (yB c₃ y) 3 (by omega) (by omega)))).trans
    ((conj_drawn hs hs _).trans ?_)
  simp only [List.map_cons, List.map_nil]
  exact drawn2_congr (bM_der m y c₃ true) (bM_der m y c₃ false)

/-- The two remainders: merged on their idle wires, four instances of (336). -/
theorem commRemRem (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ c₂))
      (swAt (m + 6) 0 * boxN (m + 6) y c₃ false * swAt (m + 6) 0) := by
  refine Comm.congr (splitA m ih x c₁ c₂).symm (splitB m ih y c₃).symm (comm_drawn _ _ ?_)
  intro a ha b hb
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    exact comm336_ge5 (m + 6) (by omega) ih _ _ c₂ c₃

/-! ## Step 5: the pairs and (339) in the frame -/

theorem wc_app2 (K N : ℕ) (a b : List Lt) : wc K N (a ++ b) = drawn [wc K N a, wc K N b] := by
  rw [wc_append, drawn_two]

theorem commRR' (m : ℕ) (ih : IH (m + 6)) {b1 b3 c1 c3 : Bool} {r h : Lt}
    (hr : r ∈ rots b1 true b3) (hh : h ∈ rots c1 false c3) :
    Comm (m + 6) (swAt (m + 6) 3 * r.circ 4 (m + 6) * swAt (m + 6) 3)
      (wc 4 (m + 6) uL' * h.circ 4 (m + 6) * wc 4 (m + 6) uL) := by
  have d := commRR_s m ih hr hh
  rw [wc_app2 5 (m + 6) [.s (.S 3), r, .s (.S 3)] (uL ++ [h] ++ uL'),
    wc_app2 5 (m + 6) (uL ++ [h] ++ uL') [.s (.S 3), r, .s (.S 3)], wc_three, wc_conj, circ_S, wc_small 5 4 _ uL uL_small.1,
    wc_small 5 4 _ uL' uL_small.2, rots_rebase hr, rots_rebase hh] at d
  exact d

theorem commArR' (m : ℕ) (ih : IH (m + 6)) (x : ℕ → Bool) (c₁ c₂ : Bool) {c1 c3 : Bool} {h : Lt}
    (hh : h ∈ rots c1 false c3) :
    Comm (m + 6) (cX 5 (m + 6) x (Ar c₁ c₂))
      (wc 4 (m + 6) uL' * h.circ 4 (m + 6) * wc 4 (m + 6) uL) := by
  have d := commAr_s m ih c₁ c₂ hh
  have hr := rots_drop4 _ _ _ h hh
  have hu := List.all_eq_true.1 uL_drop4
  have hA := Ar_drop4 c₁ c₂
  have okw : ∀ g ∈ uL ++ [h] ++ uL', g.ok 5 = true := by
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | rfl) | hg
    · have := hu g (List.mem_append_left _ hg)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1.1
    · exact hr.1
    · have := hu g (List.mem_append_right _ hg)
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1.1
  have hl : ∀ g ∈ [Ar c₁ c₂] ++ (uL ++ [h] ++ uL'), g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.mem_singleton.1 hg]; exact hA.1
    · exact okw g hg
  have hr' : ∀ g ∈ (uL ++ [h] ++ uL') ++ [Ar c₁ c₂], g.ok 5 = true := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact okw g hg
    · rw [List.mem_singleton.1 hg]; exact hA.1
  have hc := colour_wc (K := 5) (N := m + 6) (by omega) x hl hr' d
  have loc : (uL ++ [h] ++ uL').all (isLoc 5) = true := by
    have lh := rots_loc5 _ _ _ h hh
    simp only [List.all_append, List.all_cons, List.all_nil, lh, uL_loc5.1, uL_loc5.2,
      Bool.and_self]
  have eW : wcX 5 (m + 6) x (uL ++ [h] ++ uL') = wc 5 (m + 6) (uL ++ [h] ++ uL') := by
    unfold wcX wc
    congr 1
    exact List.map_congr_left (fun g hg => cX_loc x (List.all_eq_true.1 loc g hg))
  have eS : wcX 5 (m + 6) x [Ar c₁ c₂] = cX 5 (m + 6) x (Ar c₁ c₂) := by
    simp [wcX, drawn]
  have e2 : ∀ a b : List Lt, wcX 5 (m + 6) x (a ++ b) =
      drawn [wcX 5 (m + 6) x a, wcX 5 (m + 6) x b] := by
    intro a b
    simp only [wcX, List.map_append, drawn_append, drawn_two]
  rw [e2 [Ar c₁ c₂] (uL ++ [h] ++ uL'), e2 (uL ++ [h] ++ uL') [Ar c₁ c₂], eW, eS, wc_conj, wc_small 5 4 _ uL uL_small.1, wc_small 5 4 _ uL' uL_small.2,
    rots_rebase hh] at hc
  exact hc

theorem pairs339s (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    ∀ a ∈ piecesA m x c₁ c₂, ∀ b ∈ piecesB m y c₃, Comm (m + 6) a b := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha'
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hb'
  rcases pcs4_cls hg with hr | rfl <;> rcases pcs4_cls hg' with hr' | rfl
  · rw [rots_cX hr, rots_cX hr']
    exact commRR' m ih hr hr'
  · rw [rots_cX hr]
    exact Comm.congr (Derivable.refl _) (remB' m ih y c₃).symm (commRrem m ih y c₃ hr)
  · rw [rots_cX hr']
    exact Comm.congr (remA m ih x c₁ c₂).symm (Derivable.refl _) (commArR' m ih x c₁ c₂ hr')
  · exact Comm.congr (remA m ih x c₁ c₂).symm (remB' m ih y c₃).symm
      (commRemRem m ih x y c₁ c₂ c₃)

/-- (339) in the frame: the box on wire `0` black on wire `2`, the
multi-controlled `H` on the wires `1, 3` white on wire `2`. -/
theorem comm339Es (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool) :
    Comm (m + 6) (mc (m + 6) .box [0] (colOn 1 (m + 6) (xE c₁ c₂ x))) (BE (m + 6) c₃ y) :=
  Comm.congr (expA9 m ih x c₁ c₂).symm (expB9 m ih y c₃).symm
    (comm_drawn _ _ (pairs339s m ih x y c₁ c₂ c₃))

/-! ## Back to the interface -/

/-- The controls of the box of (339). -/
abbrev cA339 (N : ℕ) (x : ℕ → Bool) (c₁ c₂ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))
/-- The controls of the multi-controlled `H` of (339). -/
abbrev cB339 (N : ℕ) (y : ℕ → Bool) (c₃ : Bool) : ℕ → Option Bool :=
  ctlOr (ctlAt 0 c₃) (colOn 3 N y)

/-- (339) when the colourings are black, resp. white, on wire `3`. -/
theorem comm339_core (m : ℕ) (ih : IH (m + 6)) (x y : ℕ → Bool) (c₁ c₂ c₃ : Bool)
    (hx : x 3 = true) (hy : y 3 = false) :
    Comm (m + 6) (mc (m + 6) .box [0] (cA339 (m + 6) x c₁ c₂))
      (mc (m + 6) .hg [1, 2] (cB339 (m + 6) y c₃)) := by
  have hA := swBH ih 2 (by omega) .box (Or.inl rfl) [0] [0] (colOn 1 (m + 6) (xE c₁ c₂ x))
    (cA339 (m + 6) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cA339, colOn, ctlOr, ctlAt, xE, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  have hB := swBH ih 2 (by omega) .hg (Or.inr rfl) [1, 3] [1, 2]
    (ctlOr (ctlAt 0 c₃) (ctlOr (ctlAt 2 false) (colOn 4 (m + 6) y))) (cB339 (m + 6) y c₃) rfl
    (by decide) (by intro t ht; simp at ht; omega) rfl (fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i) with rfl | rfl | rfl | rfl | h4
      all_goals (simp only [cB339, colOn, ctlOr, ctlAt, Net.tau]; split_ifs <;>
        first | rfl | (exfalso; omega) | simp_all | omega))
  exact comm_flip (comm339Es m ih x y c₁ c₂ c₃) (swsw (m + 6) 2 (by omega)) hA hB

/-- (339) from six wires on. -/
theorem comm339_ge6 (N : ℕ) (hN : 6 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 6 := ⟨N - 6, by omega⟩
  refine sep_reduce (P := fun x y => Comm (m + 6) (mc (m + 6) .box [0] (cA339 (m + 6) x c₁ c₂))
    (mc (m + 6) .hg [1, 2] (cB339 (m + 6) y c₃))) ?_ ?_
    (fun x y hx hy => comm339_core m ih x y c₁ c₂ c₃ hx hy) x y hxy
  · intro x y j hj hjN h
    have rA := swBH ih j hjN .box (Or.inl rfl) [0] [0] (cA339 (m + 6) (x ∘ Net.tau j) c₁ c₂)
      (cA339 (m + 6) x c₁ c₂) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp [Net.tau_of_lt (show 0 < j by omega)])
      (fun i hi => by
        simp only [cA339, ctlOr, ctlAt_tau (show 2 < j by omega), ctlAt_tau (show 1 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN x hi])
    have rB := swBH ih j hjN .hg (Or.inr rfl) [1, 2] [1, 2] (cB339 (m + 6) (y ∘ Net.tau j) c₃)
      (cB339 (m + 6) y c₃) rfl (by decide) (by intro t ht; simp at ht; omega)
      (by simp [Net.tau_of_lt (show 1 < j by omega), Net.tau_of_lt (show 2 < j by omega)])
      (fun i hi => by
        simp only [cB339, ctlOr, ctlAt_tau (show 0 < j by omega),
          colOn_tau (show 3 ≤ j by omega) hjN y hi])
    exact Comm.congr rA rB (Comm.conj h (swsw _ j hjN))
  · intro x y h
    have hx := xAt_inv (m + 6) 3 (by omega)
    refine comm_flip h hx ?_ ?_
    · have e := eq81 (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂) 3 (flipAt 3 x 3)
        (by omega) (by decide) (by simp [cA339, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 6) 3, mc (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂),
          xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .box [0] (cA339 (m + 6) (flipAt 3 x) c₁ c₂) *
          xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 6) (by omega) x i
      simp only [cA339, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all
    · have e := eq81 (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃) 3 (flipAt 3 y 3)
        (by omega) (by decide) (by simp [cB339, ctlOr, ctlAt, colOn])
      rw [show drawn [xAt (m + 6) 3, mc (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃),
          xAt (m + 6) 3] = xAt (m + 6) 3 * mc (m + 6) .hg [1, 2] (cB339 (m + 6) (flipAt 3 y) c₃) *
          xAt (m + 6) 3 by simp [drawn, mul_assoc]] at e
      refine e.trans (der_of_eq (mc_congr _ _ _ (fun i hi => ?_)))
      have := colOn_flip (lo := 3) (N := m + 6) (by omega) y i
      simp only [cB339, setCtl, ctlOr, ctlAt] at this ⊢
      split_ifs at this ⊢ <;> simp_all

end QCert.RealCliffordCH.Sec8.D.N13
