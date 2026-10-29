/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (45), decoded

`D(H_[0,1]H_[7,6])` is the multi-controlled `H` on wire `0` with its box on
wire `2` (`E1`), `D(H_[0,3]H_[1,2])` the one on wire `1` with its box on wire
`0` (`E2`) and `D((-1)_[0](-1)_[1])` the box on wire `0` (`Bw`), every other
control white: the decoded rule is (146) with every wire above `2` a white
control (`Core45`, `gen/sec8/e/m45.py`).  `dec45_of` reduces the rule to that
statement; `Core45` is proved in `Core45` (`core45`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule3637
import QCert.RealCliffordCH.Sec8.E.Rule39

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

section Letters

variable (M : ℕ)

/-- `D(H_[0,1]H_[7,6])`: `H` on wire `0`, box wire `2`, every other control white. -/
abbrev E1h45 : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctl2Of 0 2 0)
/-- `D(H_[0,3]H_[1,2])`: `H` on wire `1`, box wire `0`, every other control white. -/
abbrev E2h45 : Circ (M + 3) := mc (M + 3) .hg [0, 1] (ctl2Of 0 0 1)
/-- `D((-1)_[0](-1)_[1])`: the box on wire `0`, every other control white. -/
abbrev Bw45 : Circ (M + 3) := mc (M + 3) .box [0] (colOn 1 (M + 3) fun _ => false)

/-- The decoded rule (45): (146) with every wire above `2` a white control. -/
def Core45 : Prop :=
  Derivable (theory (M + 3)) (E1h45 M * E2h45 M * E1h45 M * Bw45 M * E2h45 M)
    (E2h45 M * Bw45 M * E1h45 M * E2h45 M * E1h45 M)

end Letters

theorem patt_0176 {n : ℕ} (hn : 3 ≤ n) : patt n 0 1 7 6 = some (2, 2, 0) :=
  patt_two (s := 0) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem patt_0312 {n : ℕ} (hn : 3 ≤ n) : patt n 0 3 1 2 = some (1, 1, 0) :=
  patt_one (s := 0) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem dec_0176 {M : ℕ} : dec (M + 3) (Hh (M + 3) 0 1 7 6) = E1h45 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_patt (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold Distinct4; omega)
    (patt_0176 (by omega)), if_neg (by decide)]
  rfl

theorem dec_0312 {M : ℕ} : dec (M + 3) (Hh (M + 3) 0 3 1 2) = E2h45 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_patt (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold Distinct4; omega)
    (patt_0312 (by omega)), if_pos rfl]
  rfl

/-- (45) decodes to `Core45`. -/
theorem dec45_of {M : ℕ} (h : Core45 M) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 1 7 6, Hh (M + 3) 0 3 1 2, Hh (M + 3) 0 1 7 6,
        Zz (M + 3) 0 1, Hh (M + 3) 0 3 1 2]))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 3 1 2, Zz (M + 3) 0 1, Hh (M + 3) 0 1 7 6,
        Hh (M + 3) 0 3 1 2, Hh (M + 3) 0 1 7 6])) := by
  simp only [decW_wordOf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    dec_0176, dec_0312, dec_zz01]
  unfold Core45 at h
  simpa only [mul_assoc] using h

end QCert.RealCliffordCH.Sec8.E
