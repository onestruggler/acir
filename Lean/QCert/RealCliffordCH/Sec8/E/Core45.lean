/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (45): the decoded core

`Core45 M` (`Rule45`) is (146) with every wire above `2` a white control.

* On three wires (`M = 0`) it is (146) itself (`D.eq146`): the box wire of
  each gate is idle, so the multi-controlled `H` placed on `b :: ps` is the
  controlled `H` placed on `ps` (`placeG_shift_cons`).
* From four wires on it is `Core45Alg.alg45` in the quotient monoid of the
  theory, with the facts of `Core45Facts`: the paper's chain (pages 264–269
  of arXiv:2602.06644) regrouped into `T T = 1`, `T = k V`, `V = P₀₁ X P₀₁`,
  `X X = 1`.
-/
import QCert.RealCliffordCH.Sec8.E.Core45Facts
import QCert.RealCliffordCH.Sec8.E.Core45Alg
import QCert.RealCliffordCH.Sec8.E.Rule45
import QCert.RealCliffordCH.Sec8.D.Small

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

/-! ## The quotient monoid -/

section Quot

variable {N : ℕ}

theorem q45eq {a b : Circ N} (h : Derivable (theory N) a b) :
    (a : (conGen (theory N)).Quotient) = b := (Con.eq _).2 h

theorem q45inv {a : Circ N} (h : Derivable (theory N) (a * a) 1) :
    (a : (conGen (theory N)).Quotient) * a = 1 := by
  rw [← Con.coe_mul, ← Con.coe_one]; exact (Con.eq _).2 h

theorem q45mul {a b c : Circ N} (h : Derivable (theory N) (a * b) c) :
    (a : (conGen (theory N)).Quotient) * b = c := by
  rw [← Con.coe_mul]; exact (Con.eq _).2 h

theorem q45conj {a b c : Circ N} (h : Derivable (theory N) a (b * c * b)) :
    (a : (conGen (theory N)).Quotient) = b * c * b := by
  rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 h

theorem q45comm {a b : Circ N} (h : D.Comm N a b) :
    Commute (a : (conGen (theory N)).Quotient) b := by
  unfold D.Comm at h
  rw [D.N13.drawn_two, D.N13.drawn_two] at h
  show (a : (conGen (theory N)).Quotient) * b = b * a
  rw [← Con.coe_mul, ← Con.coe_mul]; exact (Con.eq _).2 h.symm

end Quot

/-! ## From four wires on -/

theorem core45_pos {M : ℕ} (ih : IH (M + 3)) (hM : 1 ≤ M) : Core45 M := by
  have eA : E1h45 M = gA45 M := by simp only [E1h45, gA45, ctl2Of_F]
  have eB : E2h45 M = gB45 M := by simp only [E2h45, gB45, ctl2Of_F]
  have eW : Bw45 M = gW45 M := Net.mc_congr _ _ _ (fun j hj => by
    rcases j with _ | j
    · simp [colOn, ctlF]
    · simp [colOn, ctlF, hj, bitOf])
  unfold Core45
  rw [eA, eB, eW]
  apply (Con.eq _).1
  simp only [Con.coe_mul]
  have h3 : (3 : ℕ) < M + 3 := by omega
  exact alg45 (Q := (conGen (theory (M + 3))).Quotient)
    (a := gA45 M) (b := gB45 M) (w := gW45 M) (k := gK45 M) (f := gF45 M) (v := gV45 M)
    (e := gE45 M) (P01 := gP0145 M) (P20 := gP2045 M) (P21 := gP2145 M) (beta := gBe45 M)
    (phi := gPh45 M) (zp := gZp45 M) (z := gZ45 M) (z0 := gZ045 M) (z1 := gZ145 M) (y := gY45 M)
    (y0 := gY045 M) (u0 := gU045 M) (u1 := gU145 M) (vp := gVp45 M) (p := gP45 M) (q := gQ45 M)
    (h0 := gH045 M) (h1 := gH145 M)
    (q45inv (i45box ih (t := 0) (by omega) 4)) (q45inv (i45hg ih (b := 2) (h := 0) (by omega)
      (by omega) (by omega) 0))
    (q45inv (i45hg ih (b := 0) (h := 1) (by omega) (by omega) (by omega) 0))
    (q45inv (i45box ih (t := 0) (by omega) 0))
    (q45inv (i45hg ih (b := 0) (h := 1) (by omega) (by omega) (by omega) 8))
    (q45inv (i45box ih (t := 2) (by omega) 1)) (q45inv (i45box ih (t := 2) (by omega) 0))
    (q45inv (i45box ih (t := 2) (by omega) 2)) (q45inv (i45box ih (t := 2) (by omega) 3))
    (q45inv (i45box ih (t := 3) h3 2)) (q45inv (i45box ih (t := 3) h3 3))
    (q45inv (i45hg ih (b := 2) (h := 1) (by omega) (by omega) (by omega) 0))
    (q45inv (i45hg ih (b := 2) (h := 1) (by omega) (by omega) (by omega) 1))
    (q45inv (pp_inv44 ih))
    -- the box `k` and the gate `f`
    (q45comm (f45kb ih)) (q45comm (f45kf ih))
    (q45comm (c45box ih (t := 0) (t' := 0) (by omega) (by omega) 4 0)) (q45comm (f45ka ih))
    (q45mul (f45v ih)) (q45mul (f45e ih hM)) (q45comm (f45wf ih hM)).symm
    (q45comm (f45af ih hM)).symm (q45comm (f45fb ih))
    -- Definition 2.4, Klein, (308), merges and moves
    (q45conj (f45b ih hM)) (q45conj (f45f ih hM)) (q45mul (f45zp ih hM)) (q45conj (f45a ih hM))
    (q45mul (klein43 ih).1) (q45mul (klein43 ih).2) (q45comm (f45vP ih)) (q45eq (f45vv ih))
    (q45mul (f45vp ih)) (q45mul (f45p ih)) (q45mul (f45q ih)) (q45comm (f45P12 ih hM 0)).symm
    (q45comm (f45P12 ih hM 1)).symm (q45conj (f45h0 ih hM)) (q45conj (f45h1 ih hM))
    (q45eq (f45zz ih hM)) (q45mul (f45z ih hM)) (q45comm (f45z1h0 ih hM))
    (q45comm (f45z0h1 ih hM)) (q45comm (f45h0h1 ih))
    -- boxes commute
    (q45comm (c45box ih (t := 2) (t' := 2) (by omega) (by omega) 0 2))
    (q45comm (c45box ih (t := 2) (t' := 2) (by omega) (by omega) 0 3))
    (q45comm (c45box ih (t := 2) (t' := 2) (by omega) (by omega) 2 3))
    (q45comm (c45box ih (t := 2) (t' := 2) (by omega) (by omega) 1 2))
    (q45comm (c45box ih (t := 2) (t' := 2) (by omega) (by omega) 1 3))
    (q45comm (c45box ih (t := 2) (t' := 2) (by omega) (by omega) 1 0))
    (q45comm (c45box ih (t := 3) (t' := 2) h3 (by omega) 2 0))
    (q45comm (c45box ih (t := 3) (t' := 2) h3 (by omega) 2 2))
    (q45comm (c45box ih (t := 3) (t' := 2) h3 (by omega) 2 1))
    (q45comm (c45box ih (t := 3) (t' := 2) h3 (by omega) 2 3))
    (q45comm (c45box ih (t := 3) (t' := 2) h3 (by omega) 3 0))
    (q45comm (c45box ih (t := 3) (t' := 2) h3 (by omega) 3 2))
    (q45comm (c45box ih (t := 3) (t' := 3) h3 h3 2 3))

/-! ## Three wires: (146) -/

namespace C45

private abbrev lX (q : ℕ) : List L := [L.H q, L.Z q, L.H q]

theorem colourW1 (q : ℕ) (G : Circ 3) :
    colourW 3 [q] G = circW 3 (lX q) * G * circW 3 (lX q) := by
  simp [colourW, drawn, xAt_eq, mul_assoc]

theorem colourW2 (p q : ℕ) (G : Circ 3) :
    colourW 3 [p, q] G = circW 3 (lX p ++ lX q) * G * circW 3 (lX p ++ lX q) := by
  simp [colourW, drawn, xAt_eq, lX, circW, mul_assoc]

theorem K1_eq : (L.K 1).circ 3 = (shift ch : Circ 3) := by
  show shift (place2 2 0 ch) = shift ch
  exact congrArg shift (pad_zero2 ch)

theorem K0_eq : (L.K 0).circ 3 = atBot 3 (ch : Circ 2) := by
  show place2 3 0 ch = _
  exact pad_atBot2 1 ch

theorem C1_eq : (L.C 1).circ 3 = (shift cz : Circ 3) := by
  show shift (place2 2 0 cz) = shift cz
  exact congrArg shift (pad_zero2 cz)

theorem hg20 : Derivable (theory 3) (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) ((L.K 0).circ 3) := by
  have h := placeG_shift_cons (n := 3) (ch : Circ 2) (p := 2) (ps := [0, 1]) (by decide)
    (by intro q hq; simp at hq; omega) rfl
  rw [placeG_pair 3 _ (by omega)] at h
  rw [K0_eq]; exact h

theorem eE1 : Derivable (theory 3) (E1h45 0) (circW 3 (lX 1 ++ [L.K 0] ++ lX 1)) := by
  have e : E1h45 0 = colourW 3 [1] (placeG 3 (shift (ch : Circ 2)) [2, 0, 1]) := rfl
  rw [e, colourW1, circW_append, circW_append]
  rw [show circW 3 [L.K 0] = (L.K 0).circ 3 by simp [circW, drawn]]
  exact dright _ (dleft _ hg20)

theorem eE2 : E2h45 0 = circW 3 (lX 2 ++ [L.K 1] ++ lX 2) := by
  have e : E2h45 0 = colourW 3 [2] (placeG 3 (shift (ch : Circ 2)) [0, 1, 2]) := rfl
  rw [e, colourW1, show placeG 3 (shift (ch : Circ 2)) [0, 1, 2] = (L.K 1).circ 3 by
    rw [K1_eq]; exact placeG_id 3 _, circW_append, circW_append]
  simp [circW, drawn, mul_assoc]

theorem eBw : Bw45 0 = circW 3 ((lX 1 ++ lX 2) ++ [L.C 1] ++ (lX 1 ++ lX 2)) := by
  have e : Bw45 0 = colourW 3 [1, 2] (placeG 3 (box 2) [0, 1, 2]) := rfl
  rw [e, colourW2, show placeG 3 (box 2) [0, 1, 2] = (L.C 1).circ 3 by
    rw [C1_eq]; exact placeG_id 3 _, circW_append, circW_append]
  simp [circW, drawn, mul_assoc]

end C45

theorem core45_zero (ih : IH 3) : Core45 0 := by
  have h := D.eq146 0 ih
  rw [D.N8.pad_zero3, D.N8.pad_zero3] at h
  have eL : D.l146 = circW 3 (C45.lX 1 ++ [L.K 0] ++ C45.lX 1) *
      circW 3 (C45.lX 2 ++ [L.K 1] ++ C45.lX 2) * circW 3 (C45.lX 1 ++ [L.K 0] ++ C45.lX 1) *
      circW 3 ((C45.lX 1 ++ C45.lX 2) ++ [L.C 1] ++ (C45.lX 1 ++ C45.lX 2)) *
      circW 3 (C45.lX 2 ++ [L.K 1] ++ C45.lX 2) := by
    simp only [D.l146, ← circW_append, List.cons_append, List.nil_append]
  have eR : D.r146 = circW 3 (C45.lX 2 ++ [L.K 1] ++ C45.lX 2) *
      circW 3 ((C45.lX 1 ++ C45.lX 2) ++ [L.C 1] ++ (C45.lX 1 ++ C45.lX 2)) *
      circW 3 (C45.lX 1 ++ [L.K 0] ++ C45.lX 1) * circW 3 (C45.lX 2 ++ [L.K 1] ++ C45.lX 2) *
      circW 3 (C45.lX 1 ++ [L.K 0] ++ C45.lX 1) := by
    simp only [D.r146, ← circW_append, List.cons_append, List.nil_append]
  rw [eL, eR] at h
  unfold Core45
  rw [C45.eE2, C45.eBw]
  have e1 := C45.eE1
  refine (dmul (dmul (dmul (dmul e1 (Derivable.refl _)) e1) (Derivable.refl _))
    (Derivable.refl _)).trans (h.trans ?_)
  exact dmul (dmul (dmul (dmul (Derivable.refl _) (Derivable.refl _)) e1.symm) (Derivable.refl _))
    e1.symm

/-- The decoded rule (45) at every width. -/
theorem core45 (M : ℕ) (ih : IH (M + 3)) : Core45 M := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact core45_zero ih
  · exact core45_pos ih hM

end QCert.RealCliffordCH.Sec8.E
