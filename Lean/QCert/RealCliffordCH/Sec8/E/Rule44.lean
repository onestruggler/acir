/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (44)

`D(X_[0,3]X_[1,2])` is `Bw` then `Xi` by (361) (`Bw` the box on wire `0`, black
on `1`, white above; `Xi` the `XZ` on wire `1`, white above, wire `0` idle),
and `D(H_[0,1]H_[3,2])` the gadget `G` (`H` on wire `0`, box wire `1`, white
above).  Both letters pass `G`: `Bw` by (338); `Xi` by the paper's chain
(112), (360), (354), (346), here with the controls above black first and
coloured at the end ((81)):

* `hg[0,1] = P Bx P` (Definition 2.4; on three wires the rule (18)), and the
  swap of the wires `0, 1` fixes `P = P ⊗ P` ((112)), so `G = P Bq P`, `Bq` the
  box on wire `1` black on `0`;
* `P Xi P = Zi`, the `ZX` ((360));
* `Zi` is the product of the `ZX` black and white on wire `0` ((354)), each of
  which passes `Bq` ((346) under the swap).

Every step was checked numerically at `N = 3, 4, 5` (`gen/sec8/e/m44.py`).
-/
import QCert.RealCliffordCH.Sec8.E.Eq361
import QCert.RealCliffordCH.Sec8.D.N15.E360

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

section Rule44

variable {M : ℕ} (ih : IH (M + 3))
include ih

/-- Definition 2.4 (on three wires, the rule (18)): the multi-controlled `H`
with box wire `0` is the box between two `P ⊗ P`. -/
theorem hg_pp44 : Derivable (theory (M + 3)) (mc (M + 3) .hg [0, 1] (blackOn 2 (M + 3)))
    (ppAt (M + 3) 0 1 * D.Bx (M + 3) * ppAt (M + 3) 0 1) := by
  rw [D.N15.ppAt_eq (M + 1)]
  rcases M with _ | m
  · have eH : mc 3 .hg [0, 1] (blackOn 2 3) = (shift ch : Circ 3) := Net.mc_canon .hg 1
    have eB : D.Bx 3 = (shift cz : Circ 3) := Net.mc_canon .box 2
    rw [eH, eB]
    have h18 := D.N8.rule_full Rule.e18
    rw [drawn_two, drawn_two] at h18
    have hp : Derivable (theory 3) ((pp : Circ 3) * pp) 1 := D.N13.pp_inv 0 ih
    -- `shift ch = shift ch pp pp = pp shift cz pp`
    have e1 : Derivable (theory 3) (shift ch : Circ 3) (shift ch * pp * pp) := by
      have := dleft (shift ch : Circ 3) hp; rw [mul_one, ← mul_assoc] at this; exact this.symm
    exact e1.trans (dright _ h18.symm)
  · have h := D.N13.hg_box m (fun _ => true)
    have e1 : mc (m + 2 + 2) .hg [0, 1] (colOn 2 (m + 2 + 2) fun _ => true) =
        mc (m + 1 + 3) .hg [0, 1] (blackOn 2 (m + 1 + 3)) :=
      Net.mc_congr _ _ _ (fun j hj => by simp [colOn, blackOn])
    have e2 : mc (m + 2 + 2) .box [0] (colOn 1 (m + 2 + 2) (D.N13.hgCol fun _ => true)) =
        D.Bx (m + 1 + 3) :=
      Net.mc_congr _ _ _ (fun j hj => by simp [colOn, blackOn, D.N13.hgCol])
    rw [e1, e2] at h
    rw [mul_assoc]
    exact h

theorem pp_inv44 : Derivable (theory (M + 3)) (ppAt (M + 3) 0 1 * ppAt (M + 3) 0 1) 1 := by
  rw [D.N15.ppAt_eq (M + 1)]; exact D.N13.pp_inv M ih

/-- (112): the swap of the wires `0, 1` fixes `P ⊗ P`. -/
theorem sw_pp44 : Derivable (theory (M + 3))
    (swAt (M + 3) 0 * ppAt (M + 3) 0 1 * swAt (M + 3) 0) (ppAt (M + 3) 0 1) := by
  have h := D.N15.lift2 ih (a := (swap : Circ 2) * pp * swap) (b := pp)
    (Fast.sem_of_fast (by decide +kernel))
  rw [atBot_mul, atBot_mul, D.N15.atBot_sw, D.N8.atBot_pp (M + 3) 0 (by omega)] at h
  exact h

/-- The gadget with black controls is `P Bq P`. -/
theorem gadget_pp44 : Derivable (theory (M + 3)) (mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3)))
    (ppAt (M + 3) 0 1 * mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))) *
      ppAt (M + 3) 0 1) := by
  have hsw := D.N15.mcSwapAll' ih
  set S := swAt (M + 3) 0
  set P := ppAt (M + 3) 0 1
  have hS : Derivable (theory (M + 3)) (S * S) 1 := swsw (M + 3) 0 (by omega)
  have fH : Derivable (theory (M + 3)) (S * mc (M + 3) .hg [0, 1] (blackOn 2 (M + 3)) * S)
      (mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3))) := by
    have h := hsw 0 (by omega) .hg [0, 1] (blackOn 2 (M + 3)) rfl (by simp) (by simp)
    rw [D.N15.conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([0, 1] : List ℕ).map (Net.tau 0) = [1, 0] by simp [Net.tau]]
    exact Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | j <;> simp [Function.comp, Net.tau, blackOn])
  have fB : Derivable (theory (M + 3)) (S * D.Bx (M + 3) * S)
      (mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))) := by
    have h := hsw 0 (by omega) .box [0] (blackOn 1 (M + 3)) rfl (by simp) (by simp)
    rw [D.N15.conj3] at h
    refine h.trans (der_of_eq ?_)
    rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
    exact Net.mc_congr _ _ _ (fun j hj => by
      rcases j with _ | _ | j <;> simp [Function.comp, Net.tau, blackOn, ctlOr, ctlAt] <;> omega)
  have k := D.N15.via_conj hS (l := [mc (M + 3) .hg [0, 1] (blackOn 2 (M + 3))])
    (L := [mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3))]) (r := [P, D.Bx (M + 3), P])
    (R := [P, mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))), P])
    (List.Forall₂.cons fH List.Forall₂.nil)
    (List.Forall₂.cons (sw_pp44 ih) (List.Forall₂.cons fB (List.Forall₂.cons (sw_pp44 ih)
      List.Forall₂.nil)))
    (by rw [D.N15.drawn_one', D.N15.drawn_three']; exact hg_pp44 ih)
  rwa [D.N15.drawn_one', D.N15.drawn_three'] at k

/-- The `ZX` on wire `1` (wire `0` idle) passes the box on wire `1`. -/
theorem zi_bq44 : D.Comm (M + 3) (mc (M + 3) .zx [1] (blackOn 2 (M + 3)))
    (mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))) := by
  have hsw := D.N15.mcSwapAll' ih
  set S := swAt (M + 3) 0
  have hS : Derivable (theory (M + 3)) (S * S) 1 := swsw (M + 3) 0 (by omega)
  set Bq := mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3)))
  have one : ∀ b : Bool, D.Comm (M + 3) (mc (M + 3) (Kind.sgnZX false) [1]
      (setCtl (blackOn 2 (M + 3)) 0 (some b))) Bq := by
    intro b
    set y : ℕ → Bool := fun j => if j = 1 then b else true
    have h := D.eq346 (M + 3) (by omega) ih (fun _ => true) y false
    have hc := D.N13.Comm.conj h hS (u := S) (v := S)
    refine Derivable.symm ?_
    refine D.N13.Comm.congr ?_ ?_ hc
    · have h1 := hsw 0 (by omega) .box [0] (colOn 1 (M + 3) fun _ => true) rfl (by simp) (by simp)
      rw [D.N15.conj3] at h1
      refine h1.trans (der_of_eq ?_)
      rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
      exact Net.mc_congr _ _ _ (fun j hj => by
        rcases j with _ | _ | j <;> simp [Function.comp, Net.tau, colOn, blackOn, ctlOr, ctlAt] <;>
          omega)
    · have h1 := hsw 0 (by omega) (Kind.sgnZX false) [0] (colOn 1 (M + 3) y) rfl (by simp)
        (by simp)
      rw [D.N15.conj3] at h1
      refine h1.trans (der_of_eq ?_)
      rw [show ([0] : List ℕ).map (Net.tau 0) = [1] by simp [Net.tau]]
      exact Net.mc_congr _ _ _ (fun j hj => by
        rcases j with _ | _ | j <;> simp [Function.comp, Net.tau, colOn, blackOn, setCtl, y] <;>
          omega)
  have hm := mergeAtZ ih false (t := 1) (by omega) (blackOn 2 (M + 3)) (by simp [blackOn])
    (w := 0) (by omega) (by omega) true
  have e : mc (M + 3) (Kind.sgnZX false) [1] (setCtl (blackOn 2 (M + 3)) 0 none) =
      mc (M + 3) .zx [1] (blackOn 2 (M + 3)) :=
    Net.mc_congr _ _ _ (fun j hj => by rcases j with _ | j <;> simp [setCtl, blackOn])
  rw [e, drawn_two] at hm
  exact D.N13.Comm.congr hm (Derivable.refl _) (D.N13.Comm.mul_left (one false) (one true))

omit ih in
/-- The algebra: `Xi` passes `G = P Bq P` when `P Xi P = Zi` passes `Bq`. -/
theorem alg44 {Q : Type*} [Monoid Q] {P Xi Zi Bq G : Q} (hP : P * P = 1) (hZ : P * Xi * P = Zi)
    (hG : G = P * Bq * P) (hc : Zi * Bq = Bq * Zi) : Xi * G = G * Xi := by
  have hXP : Xi * P = P * Zi := by
    calc Xi * P = (P * P) * Xi * P := by rw [hP, one_mul]
      _ = P * Zi := by rw [← hZ]; simp only [mul_assoc]
  have hZP : Zi * P = P * Xi := by
    calc Zi * P = P * Xi * (P * P) := by rw [← hZ]; simp only [mul_assoc]
      _ = P * Xi := by rw [hP, mul_one]
  calc Xi * G = Xi * P * Bq * P := by rw [hG]; simp only [mul_assoc]
    _ = P * (Zi * Bq) * P := by rw [hXP]; simp only [mul_assoc]
    _ = P * Bq * (Zi * P) := by rw [hc]; simp only [mul_assoc]
    _ = G * Xi := by rw [hZP, hG]; simp only [mul_assoc]

/-- `Xi` with black controls passes the gadget with black controls. -/
theorem xi_g_black : D.Comm (M + 3) (mc (M + 3) .xz [1] (blackOn 2 (M + 3)))
    (mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3))) := by
  set P := ppAt (M + 3) 0 1
  have h360 := D.eq360 (M + 3) (by omega) ih
  rw [drawn_two, drawn_two] at h360
  have hP := pp_inv44 ih
  -- `P Xi P = Zi`
  have hZ : Derivable (theory (M + 3)) (P * mc (M + 3) .xz [1] (blackOn 2 (M + 3)) * P)
      (mc (M + 3) .zx [1] (blackOn 2 (M + 3))) := by
    refine (dright _ h360.symm).trans ?_
    rw [mul_assoc]
    have := dleft (mc (M + 3) .zx [1] (blackOn 2 (M + 3))) hP
    rwa [mul_one] at this
  have hc := zi_bq44 ih
  unfold D.Comm at hc
  rw [drawn_two, drawn_two] at hc
  have key := alg44 (Q := (conGen (theory (M + 3))).Quotient)
    (P := (P : (conGen (theory (M + 3))).Quotient)) (Xi := mc (M + 3) .xz [1] (blackOn 2 (M + 3)))
    (Zi := mc (M + 3) .zx [1] (blackOn 2 (M + 3)))
    (Bq := mc (M + 3) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (M + 3))))
    (G := mc (M + 3) .hg [1, 0] (blackOn 2 (M + 3)))
    (by rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 hP)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hZ)
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 (gadget_pp44 ih))
    (by rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 hc.symm)
  unfold D.Comm
  rw [drawn_two, drawn_two]
  apply (Con.eq _).1
  rw [Con.coe_mul, Con.coe_mul]
  exact key.symm

/-- The same with the controls above white ((81)). -/
theorem xi_g_white : D.Comm (M + 3) (mc (M + 3) .xz [1] (colOn 2 (M + 3) fun _ => false))
    (mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false)) := by
  set ws := D.N15.S8 M
  have hnd : ws.Nodup := D.N15.S8_nodup
  have hu := D.xs_inv (M + 3) ws hnd (fun w hw => (D.N15.mem_S8.1 hw).2)
  set u := drawn (ws.map (xAt (M + 3)))
  have colr : ∀ (K : Kind) (tg : List ℕ), (∀ t ∈ tg, t < 2) →
      Derivable (theory (M + 3)) (u * mc (M + 3) K tg (blackOn 2 (M + 3)) * u)
        (mc (M + 3) K tg (colOn 2 (M + 3) fun _ => false)) := by
    intro K tg htg
    have h := D.N13.mc_colour (M + 3) K tg (blackOn 2 (M + 3)) ws hnd (fun j hj => by
      have := D.N15.mem_S8.1 hj
      refine ⟨this.2, fun h => by have := htg j h; omega, ?_⟩
      simp only [blackOn]; rw [if_pos ⟨this.1, this.2⟩])
    rw [Net.colourW_eq] at h
    refine h.trans (der_of_eq (Net.mc_congr _ _ _ (fun j hj => ?_)))
    by_cases hjw : j ∈ ws
    · have := D.N15.mem_S8.1 hjw
      rw [if_pos hjw]; simp [colOn, this.1, hj]
    · rw [if_neg hjw]
      have : j < 2 := by by_contra h; exact hjw (D.N15.mem_S8.2 ⟨by omega, hj⟩)
      have h2 : ¬ 2 ≤ j := by omega
      simp [colOn, blackOn, h2]
  have hc := D.N13.Comm.conj (xi_g_black ih) hu (u := u) (v := u)
  exact D.N13.Comm.congr (colr .xz [1] (by simp)) (colr .hg [1, 0] (by simp)) hc

end Rule44

/-- (44) decodes to (361), (338) and `xi_g_white`. -/
theorem dec44 {M : ℕ} (ih : IH (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Xx (M + 3) 0 3 1 2, Hh (M + 3) 0 1 3 2]))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 1 3 2, Xx (M + 3) 0 3 1 2])) := by
  have h361 := D.eq361 (M + 3) (by omega) ih
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one] at h361 ⊢
  rw [dec_0132 (by omega : 3 ≤ M + 3), gadget_colOn]
  rw [drawn_two] at h361
  set G := mc (M + 3) .hg [1, 0] (colOn 2 (M + 3) fun _ => false)
  set Bw := mc (M + 3) .box [0] (ctlOr (ctlAt 1 true) (colOn 2 (M + 3) fun _ => false))
  set Xi := mc (M + 3) .xz [1] (colOn 2 (M + 3) fun _ => false)
  have cB := D.eq338 (M + 3) (by omega) ih (fun _ => false) (fun _ => false) true
  have cX := xi_g_white ih
  have c := D.N13.Comm.mul_left cX cB
  unfold D.Comm at c
  rw [drawn_two, drawn_two] at c
  -- `D G = (Xi Bw) G = G (Xi Bw) = G D`
  exact (dright _ h361).trans (c.symm.trans (dleft _ h361.symm))

end QCert.RealCliffordCH.Sec8.E
