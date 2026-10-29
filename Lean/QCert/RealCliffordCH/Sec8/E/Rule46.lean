/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (46), decoded

The decoded letters (`gen/sec8/e/m46.py`), every wire above `2` a white
control:

* `D(H_[0,1]H_[7,6])` is `A`, the multi-controlled `H` on wire `0` with its box
  on wire `2`, white on `1`;
* `D(H_[0,3]H_[1,2])` is `B`, `H` on wire `1`, box wire `0`, white on `2`;
* `D(H_[3,4]H_[2,5])` is `Cc`, `H` on wire `2`, box wire `0`, black on `1`;
* `D(H_[3,2]H_[4,5])` is `Dd`, `H` on wire `0`, box wire `2`, black on `1`;
* `D(H_[7,6]H_[4,5])` is `F`, `H` on wire `0`, box wire `1`, black on `2`;
* `D((-1)_[2](-1)_[3])` is `Z`, the box on wire `0`, black on `1`, white on `2`.

The decoded rule is `A B Cc Dd F Z Cc B = B Cc Z F Dd Cc B A` (monoid order):
(147) with every wire above `2` a white control (`Core46`).  `dec46_of`
reduces the rule (46) to that statement.
-/
import QCert.RealCliffordCH.Sec8.E.Rule45

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

section Letters

variable (M : ℕ)

/-- `D(H_[0,1]H_[7,6])`: `H` on wire `0`, box wire `2`, every other control white. -/
abbrev A46 : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctl2Of 0 2 0)
/-- `D(H_[0,3]H_[1,2])`: `H` on wire `1`, box wire `0`, every other control white. -/
abbrev B46 : Circ (M + 3) := mc (M + 3) .hg [0, 1] (ctl2Of 0 0 1)
/-- `D(H_[3,4]H_[2,5])`: `H` on wire `2`, box wire `0`, black on `1`. -/
abbrev C46 : Circ (M + 3) := mc (M + 3) .hg [0, 2] (ctl2Of 2 0 2)
/-- `D(H_[3,2]H_[4,5])`: `H` on wire `0`, box wire `2`, black on `1`. -/
abbrev D46 : Circ (M + 3) := mc (M + 3) .hg [2, 0] (ctl2Of 2 2 0)
/-- `D(H_[7,6]H_[4,5])`: `H` on wire `0`, box wire `1`, black on `2`. -/
abbrev F46 : Circ (M + 3) := mc (M + 3) .hg [1, 0] (ctl2Of 4 1 0)
/-- `D((-1)_[2](-1)_[3])`: the box on wire `0`, black on `1`, white on `2`. -/
abbrev Z46 : Circ (M + 3) := mc (M + 3) .box [0] (ctlOf 3 0)

/-- The decoded rule (46): (147) with every wire above `2` a white control. -/
def Core46 : Prop :=
  Derivable (theory (M + 3))
    (A46 M * B46 M * C46 M * D46 M * F46 M * Z46 M * C46 M * B46 M)
    (B46 M * C46 M * Z46 M * F46 M * D46 M * C46 M * B46 M * A46 M)

end Letters

theorem patt_3425 {n : ℕ} (hn : 3 ≤ n) : patt n 3 4 2 5 = some (1, 2, 0) :=
  patt_one (s := 2) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem patt_3245 {n : ℕ} (hn : 3 ≤ n) : patt n 3 2 4 5 = some (2, 2, 0) :=
  patt_two (s := 2) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem patt_7645 {n : ℕ} (hn : 3 ≤ n) : patt n 7 6 4 5 = some (2, 1, 0) :=
  patt_two (s := 4) (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem dec_3425 {M : ℕ} : dec (M + 3) (Hh (M + 3) 3 4 2 5) = C46 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_patt (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold Distinct4; omega)
    (patt_3425 (by omega)), if_pos rfl]
  rfl

theorem dec_3245 {M : ℕ} : dec (M + 3) (Hh (M + 3) 3 2 4 5) = D46 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_patt (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold Distinct4; omega)
    (patt_3245 (by omega)), if_neg (by decide)]
  rfl

theorem dec_7645 {M : ℕ} : dec (M + 3) (Hh (M + 3) 7 6 4 5) = F46 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_patt (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold Distinct4; omega)
    (patt_7645 (by omega)), if_neg (by decide)]
  rfl

theorem isOnes_two : IsOnes 2 0 := ⟨fun j hj => absurd hj (by omega), by decide⟩

/-- `D((-1)_[2](-1)_[3])`. -/
theorem dec_zz23 {M : ℕ} : dec (M + 3) (Zz (M + 3) 2 3) = Z46 M := by
  have h8 := two_pow_ge8 (M := M)
  rw [dec_Zz (by omega) (by omega), show dZZ (M + 3) 2 3 = dZZ (M + 3) 2 (2 + 1) from rfl,
    dZZ_succ, dZZ1_mc (M + 2), tOf_eq isOnes_two (by have := two_pow_ge8' (M := M); omega)]
  rfl

/-- (46) decodes to `Core46`. -/
theorem dec46_of {M : ℕ} (h : Core46 M) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 1 7 6, Hh (M + 3) 0 3 1 2, Hh (M + 3) 3 4 2 5,
        Hh (M + 3) 3 2 4 5, Hh (M + 3) 7 6 4 5, Zz (M + 3) 2 3, Hh (M + 3) 3 4 2 5,
        Hh (M + 3) 0 3 1 2]))
      (decW (M + 3) (wordOf [Hh (M + 3) 0 3 1 2, Hh (M + 3) 3 4 2 5, Zz (M + 3) 2 3,
        Hh (M + 3) 7 6 4 5, Hh (M + 3) 3 2 4 5, Hh (M + 3) 3 4 2 5, Hh (M + 3) 0 3 1 2,
        Hh (M + 3) 0 1 7 6])) := by
  simp only [decW_wordOf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    dec_0176, dec_0312, dec_3425, dec_3245, dec_7645, dec_zz23]
  unfold Core46 at h
  simpa only [mul_assoc] using h

end QCert.RealCliffordCH.Sec8.E
