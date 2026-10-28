/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rules (23), (29) and (41)

Each side of these rules decodes to gates on one or two wires with the
same controls; moved to the canonical position by a frame (`frame1`,
`frame2`), the rule is (355), (317) or (312).

* (23): `D((-1)_[a](-1)_[a+1])` is the box and `D((-1)_[a]X_[a,a+1])` the
  multi-controlled `(-1)^β XZ` on the same wire with the same controls, and
  (355) says the square of the latter is the former.
* (29): `D((-1)_[a]X_[a,a+1])` and `D((-1)_[a+1]X_[a,a+1])` are the
  multi-controlled `XZ` and `ZX` (in some order), inverse by (317).
* (41): `D(H_[0,1]H_[3,2])` is the multi-controlled `H` with its box on
  wire `1`, `H` on wire `0` and white controls, an involution by (312).
-/
import QCert.RealCliffordCH.Sec8.E.Lemma87H

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Frames at one and two wires -/

/-- The colours of the canonical gate for a gate on wire `t` coloured by `s`. -/
def pull1 (t s : ℕ) : ℕ → Bool := fun j => decide (bitOf s (frm [t] j) = 1)

theorem frame1 {N : ℕ} (ih : IH N) (K : Kind) (hK : kindSp K = 1) {t : ℕ} (ht : t < N) (s : ℕ) :
    Derivable (theory N) (placedBy N (netOf [t]) (mc N K [0] (colOn 1 N (pull1 t s))))
      (mc N K [t] (ctlOf s t)) := by
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < N := by simp [ht]
  have h0 : frm [t] 0 = t := frm_getD hnd hps (by simp)
  have := frame (mcSwapAll ih) hnd hps K [0] (ctlOf s t) (by simp [hK]) (by simp) (by simp; omega)
  rw [show [0].map (frm [t]) = [t] by simp [h0]] at this
  refine Derivable.trans ?_ this
  rw [Net.mc_congr N K [0] (c := colOn 1 N (pull1 t s)) (c' := ctlOf s t ∘ frm [t]) ?_]
  intro j hj
  rcases j with _ | j
  · simp [colOn, ctlOf, h0]
  · have hne : frm [t] (j + 1) ≠ t := by
      intro e; have := frm_injective [t] (e.trans h0.symm); omega
    simp [colOn, ctlOf, hne, pull1, hj]

/-- The colours of the canonical gate for a gate on the wires `b`, `h`
coloured by `s`. -/
def pull2 (b h s : ℕ) : ℕ → Bool := fun j => decide (bitOf s (frm [b, h] j) = 1)

theorem frame2 {N : ℕ} (ih : IH N) (K : Kind) (hK : kindSp K = 2) {b h : ℕ} (hb : b < N)
    (hh : h < N) (hbh : b ≠ h) (s : ℕ) :
    Derivable (theory N) (placedBy N (netOf [b, h]) (mc N K [0, 1] (colOn 2 N (pull2 b h s))))
      (mc N K [b, h] (ctl2Of s b h)) := by
  have hnd : [b, h].Nodup := by simp [hbh]
  have hps : ∀ p ∈ [b, h], p < N := by simp [hb, hh]
  have h0 : frm [b, h] 0 = b := frm_getD hnd hps (by simp)
  have h1 : frm [b, h] 1 = h := frm_getD hnd hps (by simp)
  have := frame (mcSwapAll ih) hnd hps K [0, 1] (ctl2Of s b h) (by simp [hK]) (by simp)
    (by simp; omega)
  rw [show [0, 1].map (frm [b, h]) = [b, h] by simp [h0, h1]] at this
  refine Derivable.trans ?_ this
  rw [Net.mc_congr N K [0, 1] (c := colOn 2 N (pull2 b h s)) (c' := ctl2Of s b h ∘ frm [b, h]) ?_]
  intro j hj
  rcases j with _ | _ | j
  · simp [colOn, ctl2Of, h0]
  · simp [colOn, ctl2Of, h1]
  · have hne1 : frm [b, h] (j + 2) ≠ b := by
      intro e; have := frm_injective _ (e.trans h0.symm); omega
    have hne2 : frm [b, h] (j + 2) ≠ h := by
      intro e; have := frm_injective _ (e.trans h1.symm); omega
    simp [colOn, ctl2Of, hne1, hne2, pull2, hj]

/-! ## The decoded `ZX` letters -/

theorem dZX1_pair {k a : ℕ} :
    (kindZX (k + 1) a 0 = .xz ∧ kindZX (k + 1) a 1 = .zx) ∨
      (kindZX (k + 1) a 0 = .zx ∧ kindZX (k + 1) a 1 = .xz) := by
  unfold kindZX
  by_cases h : bitOf (gray a) (tOf (k + 1) a) = 0
  · left; simp [h]
  · right; simp [h]

theorem dec_Zx_lo {n a : ℕ} (ha : a + 1 < 2 ^ n) :
    dec n (Zx n a a (a + 1)) = dZX1 n a 0 := by
  rw [dec_Zx (by omega) (by omega) ha (by omega), dZX_lt (by omega) (Or.inl rfl),
    show a + 1 - a = 1 by omega, dZXab_one]
  simp

theorem dec_Zx_hi {n a : ℕ} (ha : a + 1 < 2 ^ n) :
    dec n (Zx n (a + 1) a (a + 1)) = dZX1 n a 1 := by
  rw [dec_Zx ha (by omega) ha (by omega), dZX_lt (by omega) (Or.inr rfl),
    show a + 1 - a = 1 by omega, dZXab_one]
  simp

/-! ## The rules -/

/-- (29) decodes to (317). -/
theorem dec29 {M : ℕ} (ih : IH (M + 3)) (a : ℕ) (ha : a + 1 < 2 ^ (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Zx (M + 3) a a (a + 1), Zx (M + 3) (a + 1) a (a + 1)]))
      (decW (M + 3) (wordOf [])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one, dec_Zx_lo ha, dec_Zx_hi ha]
  rw [dZX1_mc (M + 2), dZX1_mc (M + 2)]
  set t := tOf (M + 2 + 1) a
  have ht : t < M + 3 := tOf_lt a (by omega)
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have f := fun K hK => frame1 ih K hK ht (gray a)
  have h317 := D.eq317 (M + 3) (by omega) ih (pull1 t (gray a))
  rcases dZX1_pair (k := M + 2) (a := a) with ⟨e0, e1⟩ | ⟨e0, e1⟩ <;> rw [e0, e1]
  · have := via_frame hnd hps (L := [mc (M + 3) .zx [t] (ctlOf (gray a) t),
      mc (M + 3) .xz [t] (ctlOf (gray a) t)]) (R := []) (List.Forall₂.cons (f .zx rfl)
      (List.Forall₂.cons (f .xz rfl) List.Forall₂.nil)) List.Forall₂.nil (by simpa [drawn] using h317.1)
    simpa [drawn] using this
  · have := via_frame hnd hps (L := [mc (M + 3) .xz [t] (ctlOf (gray a) t),
      mc (M + 3) .zx [t] (ctlOf (gray a) t)]) (R := []) (List.Forall₂.cons (f .xz rfl)
      (List.Forall₂.cons (f .zx rfl) List.Forall₂.nil)) List.Forall₂.nil (by simpa [drawn] using h317.2)
    simpa [drawn] using this

/-- (23) decodes to (355). -/
theorem dec23 {M : ℕ} (ih : IH (M + 3)) (a : ℕ) (ha : a + 1 < 2 ^ (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Zz (M + 3) a (a + 1)]))
      (decW (M + 3) (wordOf [Zx (M + 3) a a (a + 1), Zx (M + 3) a a (a + 1)])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one, dec_Zx_lo ha,
    dec_Zz (by omega : a < 2 ^ (M + 3)) ha, dZZ_succ]
  rw [dZZ1_mc (M + 2), dZX1_mc (M + 2)]
  set t := tOf (M + 2 + 1) a
  have ht : t < M + 3 := tOf_lt a (by omega)
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have f := fun K hK => frame1 ih K hK ht (gray a)
  have key : ∀ b : Bool, Derivable (theory (M + 3))
      (mc (M + 3) .box [t] (ctlOf (gray a) t))
      (mc (M + 3) (Kind.sgnZX b) [t] (ctlOf (gray a) t) * mc (M + 3) (Kind.sgnZX b) [t] (ctlOf (gray a) t)) := by
    intro b
    have hK : kindSp (Kind.sgnZX b) = 1 := by cases b <;> rfl
    have := via_frame hnd hps (L := [mc (M + 3) (Kind.sgnZX b) [t] (ctlOf (gray a) t),
      mc (M + 3) (Kind.sgnZX b) [t] (ctlOf (gray a) t)]) (R := [mc (M + 3) .box [t] (ctlOf (gray a) t)])
      (List.Forall₂.cons (f _ hK) (List.Forall₂.cons (f _ hK) List.Forall₂.nil))
      (List.Forall₂.cons (f .box rfl) List.Forall₂.nil)
      (by rw [drawn_single]; exact D.eq355 (M + 3) (by omega) ih b (pull1 t (gray a)))
    rw [drawn_single, drawn_two] at this
    exact this.symm
  rcases dZX1_pair (k := M + 2) (a := a) with ⟨e0, _⟩ | ⟨e0, _⟩ <;> rw [e0]
  · exact key true
  · exact key false

theorem gadget_mc (k : ℕ) : gadget (k + 2) = mc (k + 2) .hg [1, 0] (ctl2Of 0 1 0) := by
  unfold gadget
  rw [← placeAt2_mc k 0 1 0 (by omega) (by omega) (by omega)]
  congr 1
  · funext j; simp [bitOf]
  · funext j; rcases j with _ | _ | j <;> simp

/-- (41) decodes to (312). -/
theorem dec41 {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Hh (M + 3) 0 1 3 2, Hh (M + 3) 0 1 3 2]))
      (decW (M + 3) (wordOf [])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_0132 (by omega : 3 ≤ M + 3)]
  rw [show M + 3 = (M + 1) + 2 from rfl, gadget_mc]
  have hnd : [1, 0].Nodup := by simp
  have hps : ∀ p ∈ [1, 0], p < M + 1 + 2 := by simp
  have f := frame2 ih .hg rfl (b := 1) (h := 0) (by omega) (by omega) (by omega) 0
  have := via_frame hnd hps (L := [mc (M + 1 + 2) .hg [1, 0] (ctl2Of 0 1 0),
    mc (M + 1 + 2) .hg [1, 0] (ctl2Of 0 1 0)]) (R := []) (List.Forall₂.cons f
    (List.Forall₂.cons f List.Forall₂.nil)) List.Forall₂.nil
    (by simpa [drawn] using D.eq312 (M + 1 + 2) (by omega) ih (pull2 1 0 0))
  simpa [drawn] using this

end QCert.RealCliffordCH.Sec8.E
