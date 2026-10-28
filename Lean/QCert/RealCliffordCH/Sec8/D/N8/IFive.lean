/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The interface statements of package (iv) from five wires on

The runs of `S290`, `S300`, `S314` on five local wires, read in the
conventions of `MC` at every width `m + 5`: each letter is the `mc` gate of
the interface (`Net.mc_congr`, the controls compared wire by wire).
-/
import QCert.RealCliffordCH.Sec8.D.N8.S314
import QCert.RealCliffordCH.Sec8.D.N8.I269

namespace QCert.RealCliffordCH.Sec8.D.N8

open Circuit Eng SE Net

set_option linter.unusedSimpArgs false

/-- Controls of a letter on five local wires, read on `m + 5` wires. -/
theorem ctl5_eq {m : ℕ} {cs : List (ℕ × Bool)} {b : Bool} {c : ℕ → Option Bool}
    (hlo : ∀ i < 5, cs.lookup i = c i)
    (hhi : ∀ i, 5 ≤ i → i < m + 5 → c i = if b then some true else none) :
    ∀ i < m + 5, ctl 5 cs b i = c i := by
  intro i hi
  by_cases h : i < 5
  · simp [ctl, h, hlo i h]
  · simp only [ctl, if_neg h, hhi i (by omega) hi]

set_option linter.unusedSimpArgs false in
/-- The controls of the interface on the wires below `5`, for every gate used here. -/
theorem lo5_aux (m i : ℕ) (hi : i < 5) : i < m + 5 := by omega

theorem bx0_mc (m : ℕ) : bx0.circ 5 (m + 5) = BxI (m + 5) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem cC_mc (m : ℕ) : cC.circ 5 (m + 5) = Bx1I (m + 5) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem wW_mc (m : ℕ) : wW.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 3) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem wV_mc (m : ℕ) : wV.circ 5 (m + 5) = mc (m + 5) .xz [0] (blackOn 1 3) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem eA_mc (m : ℕ) :
    eA.circ 5 (m + 5) = mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 5))) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem eA_mc' (m : ℕ) :
    eA.circ 5 (m + 5) = mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 none) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem D4_mc (m : ℕ) :
    D4.circ 5 (m + 5) = mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5))) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem Z123_mc (m : ℕ) : Z123.circ 5 (m + 5) = mc (m + 5) .zx [0] (blackOn 1 4) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem X123_mc (m : ℕ) : X123.circ 5 (m + 5) = mc (m + 5) .xz [0] (blackOn 1 4) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem A2z_mc (m : ℕ) :
    A2z.circ 5 (m + 5) = mc (m + 5) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem A2x_mc (m : ℕ) :
    A2x.circ 5 (m + 5) = mc (m + 5) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem Bw_mc (m : ℕ) :
    Bw.circ 5 (m + 5) =
      mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 (m + 5)))) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem Bx2w_mc (m : ℕ) :
    Bx2w.circ 5 (m + 5) = mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 (some false)) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem V1_mc (m : ℕ) : V1.circ 5 (m + 5) = mc (m + 5) .xz [0] (ctlAt 1 true) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem W1_mc (m : ℕ) : W1.circ 5 (m + 5) = mc (m + 5) .zx [0] (ctlAt 1 true) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem bx1p_mc (m : ℕ) :
    bx1p.circ 5 (m + 5) = mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 5))) := by
  have e : bx1p = .g .box [1] [(0, true), (2, true), (3, true), (4, true)] true := by decide
  rw [e]
  exact mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem hgF_mc (m : ℕ) : hgF.circ 5 (m + 5) = mc (m + 5) .hg [0, 1] (blackOn 2 (m + 5)) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem hg12_circ_mc (m : ℕ) : hg12.circ 5 (m + 5) = mc (m + 5) .hg [1, 2] (blackOn 3 (m + 5)) :=
  mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem B1_mc' (m : ℕ) : B1.circ 5 (m + 5) = mc (m + 5) .box [1] (blackOn 2 (m + 5)) := by
  rw [B1_eq]
  exact mc_congr _ _ _ (ctl5_eq
    (fun i hi => by have hiN := lo5_aux m i hi; rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, hiN] <;> decide)
    (fun i h1 h2 => by simp [blackOn, ctlOr, ctlAt, setCtl, Option.or, h2, show ¬ i < 3 by omega, show ¬ i < 4 by omega, show ¬ i < 5 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show 1 ≤ i by omega, show 2 ≤ i by omega, show 3 ≤ i by omega, show 4 ≤ i by omega]))

theorem wc2 (K N : ℕ) (x y : Lt) : wc K N [x, y] = drawn [x.circ K N, y.circ K N] := rfl
theorem wc4 (K N : ℕ) (x y z t : Lt) :
    wc K N [x, y, z, t] = drawn [x.circ K N, y.circ K N, z.circ K N, t.circ K N] := rfl

/-! ## The statements from five wires on -/

theorem eq290_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5))
      (drawn [mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5))),
        mc (m + 5) .zx [0] (blackOn 1 4)])
      (drawn [mc (m + 5) .zx [0] (blackOn 1 4),
        mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5)))]) := by
  have h := s290 m ih
  rw [wc2, wc2, D4_mc, Z123_mc] at h
  exact h

theorem eq291_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5))
      (drawn [mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 5))),
        mc (m + 5) .zx [0] (blackOn 1 4)])
      (drawn [mc (m + 5) .zx [0] (blackOn 1 4),
        mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 3 (m + 5)))]) := by
  have h := s291i m ih
  rw [wc2, wc2, eA_mc, Z123_mc] at h
  exact h

theorem eq292_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5))
      (drawn [mc (m + 5) .zx [0] (blackOn 1 3),
        mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 (m + 5))))])
      (drawn [mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (ctlOr (ctlAt 2 false) (blackOn 3 (m + 5)))),
        mc (m + 5) .zx [0] (blackOn 1 3)]) := by
  have h := s292 m ih
  rw [wc2, wc2, wW_mc, Bw_mc] at h
  exact h

theorem eq295_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (BxI (m + 5))
      (drawn [mc (m + 5) .zx [0] (blackOn 1 4), mc (m + 5) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5))),
        mc (m + 5) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)), mc (m + 5) .xz [0] (blackOn 1 4),
        mc (m + 5) .zx [1] (ctlOr (ctlAt 0 true) (blackOn 2 4)),
        mc (m + 5) .box [0] (ctlOr (ctlAt 1 true) (blackOn 4 (m + 5))),
        mc (m + 5) .xz [1] (ctlOr (ctlAt 0 true) (blackOn 2 4))]) := by
  have h := s295i m ih
  rw [wc_one, bx0_mc] at h
  refine h.trans (der_of_eq ?_)
  show drawn [Z123.circ 5 (m + 5), A2z.circ 5 (m + 5), D4.circ 5 (m + 5), A2x.circ 5 (m + 5),
    X123.circ 5 (m + 5), A2z.circ 5 (m + 5), D4.circ 5 (m + 5), A2x.circ 5 (m + 5)] = _
  rw [Z123_mc, A2z_mc, D4_mc, A2x_mc, X123_mc]

theorem eq299_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (drawn [BxI (m + 5), BxI (m + 5)]) 1 := by
  have h := s299 m ih
  rw [wc2, bx0_mc] at h
  exact h

theorem eq300_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (BxI (m + 5))
      (drawn [Bx1I (m + 5), mc (m + 5) .zx [0] (blackOn 1 3), Bx1I (m + 5),
        mc (m + 5) .xz [0] (blackOn 1 3)]) := by
  have h := s300 m ih
  rw [wc_one, wc4, bx0_mc, cC_mc, wW_mc, wV_mc] at h
  exact h

theorem eq301_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5))
      (drawn [BxI (m + 5), mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 (some false))])
      (mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 none)) := by
  have h := s301 m ih
  rw [wc2, wc_one, bx0_mc, Bx2w_mc, eA_mc'] at h
  exact h

theorem eq302_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5))
      (drawn [mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 (some false)), BxI (m + 5)])
      (mc (m + 5) .box [0] (setCtl (blackOn 1 (m + 5)) 2 none)) := by
  have h := s302 m ih
  rw [wc2, wc_one, bx0_mc, Bx2w_mc, eA_mc'] at h
  exact h

theorem eq305_5 (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5))
      (drawn [mc (m + 5) .xz [0] (ctlAt 1 true),
        mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 5))),
        mc (m + 5) .zx [0] (ctlAt 1 true),
        mc (m + 5) .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 (m + 5)))])
      (BxI (m + 5)) := by
  have h := s305 m ih
  rw [wc4, wc_one, V1_mc, bx1p_mc, W1_mc, bx0_mc] at h
  exact h

/-- (275) and (306): the box commutes with the swaps of the wires `1, 2` and
`2, 3`. -/
theorem eq307_5_12 (m : ℕ) (ih : IH (m + 5)) (j : ℕ) (hj : j = 1 ∨ j = 2) :
    Derivable (theory (m + 5)) (drawn [BxI (m + 5), swAt (m + 5) j])
      (drawn [swAt (m + 5) j, BxI (m + 5)]) := by
  rcases hj with rfl | rfl
  · have h := s275 m ih
    rw [wc2, wc2, bx0_mc] at h
    exact h
  · have h := s306 m ih
    rw [wc2, wc2, bx0_mc] at h
    exact h

end QCert.RealCliffordCH.Sec8.D.N8
