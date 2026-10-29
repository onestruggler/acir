/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): rewrite rules, part 2

Equations 3.21–3.40 of the supplement to Selinger's paper (the rewrite
rules of Figures 3–7 of the paper), as equations between words of letters in
time order, in our wire numbering (the supplement numbers wires from the
top).  Each is derived from the relations of Figure 8 and the lemmas of the
supplement by a checked derivation, translated from the supplement's own
proof step by step.
-/
import QCert.SelingerClifford.Lemmas
import QCert.SelingerClifford.Boxes

namespace QCert.SelingerClifford

set_option maxRecDepth 8000

/-- Equation 3.21 (supplement: `[ZZ 0 1 A 3 1 B 2 0 1]·ω^0 = [A 2 1 B 3 0 1 X 0 ZZ 0 1 S 0 S 0 S 0 S 1 S 1 H 1]·ω^1`). -/
theorem rule_3_21 :
    Holds 2 ([Lt.CZ 0] ++ bA 3 0 ++ bB 2 0)
      (bA 2 0 ++ bB 3 0 ++ bX 1 ++ [.CZ 0, .S 1, .S 1, .S 1, .S 0, .S 0, .H 0, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL7 (db_ok_cons hL9 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 db_ok_nil)))))))))))
    (steps := [Step.mv 6 5, Step.rw 10 1 0 false, Step.mv 17 20, Step.mv 16 19, Step.mv 15 18, Step.mv 14 17, Step.mv 13 16, Step.mv 12 15,
     Step.mv 11 14, Step.mv 6 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.rw 1 8 0 false,
     Step.rw 4 0 0 true, Step.rw 5 1 0 false, Step.mv 14 22, Step.mv 13 21, Step.mv 12 20, Step.mv 11 19, Step.mv 10 18,
     Step.mv 9 17, Step.mv 8 16, Step.rw 0 22 0 false, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8,
     Step.mv 10 9, Step.mv 11 10, Step.rw 6 4 0 false, Step.mv 9 15, Step.mv 8 14, Step.rw 0 14 0 false,
     Step.rw 9 0 0 false, Step.mv 4 3, Step.mv 6 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9,
     Step.mv 12 10, Step.rw 1 5 0 false, Step.rw 2 3 0 false, Step.rw 1 2 0 false, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4,
     Step.mv 6 5, Step.rw 2 2 1 false, Step.mv 3 2, Step.mv 4 3, Step.rw 4 4 0 false, Step.rw 2 6 1 true,
     Step.rw 1 5 0 true, Step.rw 2 6 0 true, Step.rw 1 8 0 true, Step.rw 1 2 0 true, Step.mv 4 3, Step.mv 5 4,
     Step.mv 16 8, Step.mv 17 10, Step.rw 9 5 0 true, Step.mv 5 3, Step.mv 6 4, Step.mv 7 5, Step.rw 0 16 0 true,
     Step.mv 23 13, Step.mv 23 14, Step.rw 6 9 0 true, Step.mv 6 4, Step.mv 7 5, Step.mv 16 9, Step.rw 0 24 0 true,
     Step.mv 31 13, Step.mv 31 14, Step.mv 31 15, Step.mv 31 16, Step.mv 31 17, Step.mv 31 18, Step.mv 31 19,
     Step.rw 5 6 0 true, Step.mv 4 3, Step.mv 5 4, Step.rw 4 5 0 false, Step.rw 2 13 1 true, Step.rw 1 13 0 true,
     Step.mv 26 14, Step.mv 26 15, Step.mv 26 16, Step.mv 26 17, Step.mv 26 18, Step.mv 26 19, Step.rw 7 9 0 true,
     Step.mv 17 10, Step.mv 18 12, Step.rw 9 7 0 true, Step.rw 4 10 0 true, Step.rw 1 11 1 true, Step.rw 2 12 1 true,
     Step.rw 1 14 1 true, Step.rw 8 1 0 true, Step.mv 4 3, Step.rw 3 2 0 true, Step.mv 5 4, Step.mv 15 12, Step.mv 16 13,
     Step.mv 17 14])
    (by decide +kernel)

/-- Equation 3.22 (supplement: `[ZZ 0 1 A 3 1 B 3 0 1]·ω^0 = [A 2 1 B 2 0 1 H 1 S 1 H 1 ZZ 0 1 S 0 S 0 S 0 S 1 S 1 S 1 H 1]·ω^1`). -/
theorem rule_3_22 :
    Holds 2 ([Lt.CZ 0] ++ bA 3 0 ++ bB 3 0)
      (bA 2 0 ++ bB 2 0 ++ [.H 0, .S 0, .H 0, .CZ 0, .S 1, .S 1, .S 1, .S 0, .S 0, .S 0, .H 0, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL6 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 db_ok_nil)))))))))))))
    (steps := [Step.mv 8 7, Step.rw 3 5 0 false, Step.mv 7 6, Step.rw 10 4 0 false, Step.rw 12 1 0 false, Step.mv 17 30, Step.mv 16 29,
     Step.mv 15 28, Step.mv 14 27, Step.mv 13 26, Step.mv 12 25, Step.mv 11 24, Step.mv 6 5, Step.mv 8 6, Step.mv 9 7,
     Step.mv 10 8, Step.mv 11 9, Step.rw 1 8 0 false, Step.rw 9 9 0 false, Step.mv 12 11, Step.mv 14 12, Step.mv 17 13,
     Step.mv 18 14, Step.mv 19 15, Step.mv 20 16, Step.mv 21 17, Step.rw 2 11 0 false, Step.rw 1 17 1 false,
     Step.rw 2 15 1 false, Step.mv 14 11, Step.mv 15 12, Step.rw 1 11 1 false, Step.rw 4 0 0 true,
     Step.rw 5 1 0 false, Step.mv 14 24, Step.mv 13 23, Step.mv 12 22, Step.mv 11 21, Step.mv 10 20, Step.mv 9 19,
     Step.mv 8 18, Step.rw 0 24 0 false, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.mv 11 10, Step.rw 7 4 0 false, Step.mv 9 17, Step.mv 8 16, Step.rw 0 16 0 false, Step.rw 9 9 0 false,
     Step.mv 12 11, Step.mv 14 12, Step.mv 17 13, Step.mv 18 14, Step.mv 19 15, Step.rw 11 0 0 false, Step.mv 4 3,
     Step.mv 6 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.rw 1 5 0 false,
     Step.rw 2 3 0 false, Step.rw 1 2 0 false, Step.rw 9 3 0 false, Step.mv 6 5, Step.mv 8 6, Step.mv 11 7, Step.mv 12 8,
     Step.mv 13 9, Step.mv 14 10, Step.mv 15 11, Step.rw 2 5 0 false, Step.rw 1 11 1 false, Step.rw 2 9 1 false,
     Step.mv 8 5, Step.mv 9 6, Step.rw 1 5 1 false, Step.mv 3 2, Step.rw 4 3 0 false, Step.rw 2 8 1 true,
     Step.rw 2 7 0 true, Step.rw 1 4 0 true, Step.rw 0 18 0 true, Step.mv 25 11, Step.mv 25 12, Step.mv 25 13,
     Step.mv 25 14, Step.rw 8 5 0 true, Step.rw 1 2 0 true, Step.mv 4 3, Step.mv 16 7, Step.mv 17 9, Step.rw 11 4 0 true,
     Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.rw 0 20 0 true, Step.mv 27 12, Step.mv 27 13, Step.mv 27 14, Step.mv 27 15,
     Step.mv 27 16, Step.mv 27 17, Step.mv 27 18, Step.rw 6 9 0 true, Step.mv 6 4, Step.mv 16 8, Step.rw 0 23 0 true,
     Step.mv 30 12, Step.mv 30 13, Step.mv 30 14, Step.mv 30 15, Step.mv 30 16, Step.mv 30 17, Step.mv 30 18,
     Step.rw 5 5 0 true, Step.mv 4 3, Step.rw 4 4 0 false, Step.rw 2 13 1 true, Step.rw 1 8 0 true, Step.mv 25 15,
     Step.mv 25 16, Step.mv 25 17, Step.mv 25 18, Step.rw 8 9 0 true, Step.mv 21 12, Step.mv 21 13, Step.rw 7 8 0 true,
     Step.mv 17 9, Step.mv 18 11, Step.rw 0 22 0 true, Step.mv 29 15, Step.mv 29 16, Step.mv 29 17, Step.mv 29 18,
     Step.mv 29 19, Step.mv 29 20, Step.mv 29 21, Step.rw 12 5 0 true, Step.mv 3 2, Step.mv 13 9, Step.mv 14 10,
     Step.mv 15 11])
    (by decide +kernel)

/-- Equation 3.23 (supplement: `[ZZ 0 1 A 3 1 B 4 0 1]·ω^0 = [A 3 1 B 1 0 1 H 1 ZZ 0 1 S 1 S 1 S 1 H 1]·ω^0`). -/
theorem rule_3_23 :
    Holds 2 ([Lt.CZ 0] ++ bA 3 0 ++ bB 4 0)
      (bA 3 0 ++ bB 1 0 ++ [.H 0, .CZ 0, .S 0, .S 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL9 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM17 db_ok_nil)))))))))))))))
    (steps := [Step.mv 7 6, Step.mv 4 1, Step.rw 12 2 0 false, Step.mv 18 21, Step.mv 17 20, Step.mv 16 19, Step.mv 15 18, Step.mv 14 17,
     Step.mv 13 16, Step.mv 12 15, Step.mv 2 1, Step.mv 3 2, Step.mv 7 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10,
     Step.rw 1 9 0 false, Step.rw 10 9 0 false, Step.mv 12 11, Step.mv 14 12, Step.mv 9 8, Step.rw 4 9 0 false,
     Step.rw 2 8 1 true, Step.rw 2 7 0 true, Step.rw 1 9 0 true, Step.mv 3 1, Step.mv 14 6, Step.mv 15 8, Step.mv 33 12,
     Step.mv 33 13, Step.mv 33 14, Step.mv 33 15, Step.mv 33 16, Step.mv 33 17, Step.mv 33 18, Step.rw 12 2 0 true,
     Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.rw 0 21 0 true, Step.mv 28 10, Step.rw 7 6 0 true, Step.mv 4 2,
     Step.mv 10 6, Step.mv 27 10, Step.mv 27 11, Step.mv 27 12, Step.mv 27 13, Step.mv 27 14, Step.mv 27 15, Step.mv 27 16,
     Step.rw 5 3 0 true, Step.rw 1 13 0 true, Step.rw 0 19 0 true, Step.mv 26 14, Step.rw 6 10 0 true, Step.mv 25 13,
     Step.mv 25 14, Step.mv 25 15, Step.mv 25 16, Step.mv 25 17, Step.mv 25 18, Step.mv 25 19, Step.rw 9 10 0 true,
     Step.mv 19 15, Step.mv 20 16, Step.mv 21 17, Step.mv 22 18, Step.rw 11 5 0 true, Step.rw 2 8 1 true,
     Step.rw 1 11 1 true, Step.rw 0 21 0 true, Step.mv 28 12, Step.rw 6 8 1 true, Step.mv 2 1, Step.mv 5 4, Step.mv 8 7,
     Step.mv 9 8, Step.mv 10 9, Step.rw 13 2 0 true, Step.mv 2 1, Step.mv 3 2, Step.mv 6 5, Step.mv 25 14, Step.mv 25 15,
     Step.mv 25 16, Step.mv 25 17, Step.mv 25 18, Step.mv 25 19, Step.rw 8 9 1 true, Step.rw 2 8 0 true, Step.mv 13 8,
     Step.mv 14 10, Step.mv 15 12, Step.mv 16 13, Step.rw 10 6 0 true, Step.mv 13 10, Step.rw 3 9 0 true, Step.mv 14 11,
     Step.rw 3 10 0 true, Step.mv 15 12, Step.rw 3 11 0 true, Step.rw 4 12 0 true, Step.mv 12 6, Step.rw 4 13 0 true,
     Step.mv 13 7, Step.mv 21 14, Step.rw 7 10 1 true, Step.rw 1 8 0 true, Step.mv 3 1, Step.mv 10 5, Step.mv 11 6,
     Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.rw 14 0 0 true, Step.mv 3 2, Step.mv 4 3, Step.rw 4 1 0 true,
     Step.rw 1 2 0 true, Step.mv 9 8])
    (by decide +kernel)

/-- Equation 3.24 (supplement: `[H 0 B 1 0 1]·ω^0 = [B 1 0 1 H 1]·ω^0`). -/
theorem rule_3_24 :
    Holds 2 ([Lt.H 1] ++ bB 1 0)
      (bB 1 0 ++ [.H 0]) :=
  Holds.of_derives (db_ok_cons hL18 db_ok_nil)
    (steps := [Step.mv 1 0, Step.mv 7 6, Step.rw 0 1 0 false, Step.mv 6 5])
    (by decide +kernel)

/-- Equation 3.25 (supplement: `[H 0 B 2 0 1]·ω^0 = [B 4 0 1]·ω^0`). -/
theorem rule_3_25 :
    Holds 2 ([Lt.H 1] ++ bB 2 0)
      (bB 4 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [Step.mv 3 2, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.26 (supplement: `[H 0 B 3 0 1]·ω^0 = [B 3 0 1 X 0 S 1 S 1 S 1 H 1 S 1]·ω^0`). -/
theorem rule_3_26 :
    Holds 2 ([Lt.H 1] ++ bB 3 0)
      (bB 3 0 ++ bX 1 ++ [.S 0, .S 0, .S 0, .H 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hL4 (db_ok_cons hL10 (db_ok_cons hL17 db_ok_nil)))))))
    (steps := [Step.mv 5 4, Step.rw 1 0 1 false, Step.rw 3 0 0 false, Step.mv 2 1, Step.rw 1 5 1 true, Step.rw 2 6 1 true,
     Step.rw 1 8 1 true, Step.rw 2 5 0 true, Step.rw 1 8 0 true, Step.rw 0 19 0 true, Step.mv 26 9,
     Step.rw 4 5 0 true, Step.mv 25 8, Step.mv 25 9, Step.mv 25 10, Step.mv 25 11, Step.mv 25 12, Step.mv 25 13,
     Step.mv 25 14, Step.rw 5 5 0 true, Step.mv 15 10, Step.mv 16 11, Step.mv 17 12, Step.mv 18 13, Step.rw 6 0 0 true,
     Step.mv 3 2, Step.rw 3 1 0 true, Step.mv 4 3, Step.mv 11 6, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9])
    (by decide +kernel)

/-- Equation 3.27 (supplement: `[H 0 B 4 0 1]·ω^0 = [B 2 0 1]·ω^0`). -/
theorem rule_3_27 :
    Holds 2 ([Lt.H 1] ++ bB 4 0)
      (bB 2 0) :=
  Holds.of_derives (db_ok_cons hC2 db_ok_nil)
    (steps := [Step.mv 4 3, Step.rw 0 0 1 false, Step.mv 2 1])
    (by decide +kernel)

/-- Equation 3.28 (supplement: `[S 0 B 1 0 1]·ω^0 = [B 1 0 1 H 1 S 1 H 1]·ω^0`). -/
theorem rule_3_28 :
    Holds 2 ([Lt.S 1] ++ bB 1 0)
      (bB 1 0 ++ [.H 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC6 (db_ok_cons hL16 db_ok_nil))
    (steps := [Step.mv 1 0, Step.mv 7 6, Step.rw 0 1 0 false, Step.mv 3 2, Step.rw 1 3 0 false, Step.mv 6 5])
    (by decide +kernel)

/-- Equation 3.29 (supplement: `[S 0 B 2 0 1]·ω^0 = [B 3 0 1 X 0 S 1 S 1 S 1 H 1 S 1]·ω^0`). -/
theorem rule_3_29 :
    Holds 2 ([Lt.S 1] ++ bB 2 0)
      (bB 3 0 ++ bX 1 ++ [.S 0, .S 0, .S 0, .H 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hL4 (db_ok_cons hL10 (db_ok_cons hL17 db_ok_nil)))))))
    (steps := [Step.mv 3 2, Step.rw 3 0 0 false, Step.mv 2 1, Step.rw 1 5 1 true, Step.rw 2 6 1 true, Step.rw 1 8 1 true,
     Step.rw 2 5 0 true, Step.rw 1 8 0 true, Step.rw 0 19 0 true, Step.mv 26 9, Step.rw 4 5 0 true, Step.mv 25 8,
     Step.mv 25 9, Step.mv 25 10, Step.mv 25 11, Step.mv 25 12, Step.mv 25 13, Step.mv 25 14, Step.rw 5 5 0 true,
     Step.mv 15 10, Step.mv 16 11, Step.mv 17 12, Step.mv 18 13, Step.rw 6 0 0 true, Step.mv 3 2, Step.rw 3 1 0 true,
     Step.mv 4 3, Step.mv 11 6, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9])
    (by decide +kernel)

/-- Equation 3.30 (supplement: `[S 0 B 3 0 1]·ω^0 = [B 2 0 1 S 1 H 1 S 1]·ω^0`). -/
theorem rule_3_30 :
    Holds 2 ([Lt.S 1] ++ bB 3 0)
      (bB 2 0 ++ [.S 0, .H 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hL14 (db_ok_cons hL17 db_ok_nil)))))
    (steps := [Step.mv 5 4, Step.rw 2 2 0 false, Step.mv 4 3, Step.rw 4 1 0 false, Step.rw 2 0 0 false, Step.mv 2 1,
     Step.rw 3 2 0 false, Step.mv 5 4, Step.mv 7 5, Step.mv 10 6, Step.mv 11 7, Step.mv 12 8, Step.mv 13 9, Step.mv 14 10,
     Step.rw 1 4 0 false, Step.rw 0 10 1 false, Step.rw 1 8 1 false, Step.mv 7 4, Step.mv 8 5, Step.rw 0 4 1 false,
     Step.mv 2 1])
    (by decide +kernel)

/-- Equation 3.31 (supplement: `[S 0 B 4 0 1]·ω^0 = [B 4 0 1 H 1 S 1 H 1]·ω^0`). -/
theorem rule_3_31 :
    Holds 2 ([Lt.S 1] ++ bB 4 0)
      (bB 4 0 ++ [.H 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hL16 db_ok_nil)
    (steps := [Step.mv 4 3, Step.rw 0 0 0 false, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.32 (supplement: `[S 1 B 1 0 1]·ω^0 = [B 1 0 1 S 0]·ω^0`). -/
theorem rule_3_32 :
    Holds 2 ([Lt.S 0] ++ bB 1 0)
      (bB 1 0 ++ [.S 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC6 (db_ok_cons hM16 db_ok_nil)))
    (steps := [Step.mv 7 6, Step.mv 4 3, Step.rw 2 0 0 false, Step.mv 3 2, Step.mv 8 5, Step.rw 0 8 1 false, Step.rw 1 7 0 false,
     Step.mv 6 5])
    (by decide +kernel)

/-- Equation 3.33 (supplement: `[S 1 B 2 0 1]·ω^0 = [B 2 0 1 H 1 ZZ 0 1 S 0 S 1 H 1]·ω^0`). -/
theorem rule_3_33 :
    Holds 2 ([Lt.S 0] ++ bB 2 0)
      (bB 2 0 ++ [.H 0, .CZ 0, .S 1, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL7 (db_ok_cons hM15 db_ok_nil)))))))
    (steps := [Step.mv 3 2, Step.rw 3 0 0 false, Step.rw 2 5 1 true, Step.rw 1 5 0 true, Step.rw 2 6 0 true, Step.rw 1 8 0 true,
     Step.rw 0 17 0 true, Step.mv 24 9, Step.mv 24 10, Step.rw 5 5 0 true, Step.mv 3 1, Step.mv 15 6, Step.mv 16 8,
     Step.rw 0 25 0 true, Step.mv 32 12, Step.mv 32 13, Step.mv 32 14, Step.mv 32 15, Step.mv 32 16, Step.mv 32 17,
     Step.mv 32 18, Step.rw 6 2 0 true, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 4 2, Step.mv 11 6, Step.mv 19 10,
     Step.mv 19 11, Step.mv 19 12, Step.mv 19 13, Step.mv 19 14, Step.mv 19 15, Step.mv 19 16, Step.rw 4 3 0 true,
     Step.mv 2 1, Step.mv 8 6])
    (by decide +kernel)

/-- Equation 3.34 (supplement: `[S 1 B 3 0 1]·ω^0 = [B 3 0 1 H 1 ZZ 0 1 S 0 S 1 H 1]·ω^0`). -/
theorem rule_3_34 :
    Holds 2 ([Lt.S 0] ++ bB 3 0)
      (bB 3 0 ++ [.H 0, .CZ 0, .S 1, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL9 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 5 4, Step.rw 3 2 0 false, Step.mv 4 3, Step.rw 14 1 0 false, Step.rw 4 0 0 false, Step.rw 0 15 0 true,
     Step.mv 22 15, Step.mv 22 16, Step.rw 9 11 1 true, Step.mv 22 16, Step.mv 22 17, Step.mv 22 18, Step.mv 22 19,
     Step.mv 22 20, Step.mv 22 21, Step.rw 11 11 1 true, Step.rw 0 19 0 true, Step.mv 26 17, Step.mv 26 18,
     Step.mv 26 19, Step.mv 26 20, Step.rw 10 11 1 true, Step.mv 22 10, Step.rw 6 6 0 true, Step.rw 0 22 0 true,
     Step.mv 29 9, Step.mv 29 10, Step.mv 29 11, Step.mv 29 12, Step.mv 29 13, Step.mv 29 14, Step.mv 29 15,
     Step.rw 12 6 0 true, Step.mv 26 10, Step.rw 6 6 0 true, Step.mv 25 12, Step.rw 7 8 0 true, Step.mv 24 10,
     Step.mv 24 11, Step.rw 9 6 0 true, Step.mv 3 1, Step.mv 4 2, Step.mv 17 7, Step.mv 18 9, Step.rw 0 25 0 true,
     Step.mv 32 13, Step.mv 32 14, Step.mv 32 15, Step.mv 32 16, Step.mv 32 17, Step.mv 32 18, Step.mv 32 19,
     Step.rw 16 3 0 true, Step.mv 3 1, Step.mv 4 2, Step.mv 5 3, Step.rw 0 20 0 true, Step.mv 27 19, Step.mv 27 20,
     Step.mv 27 21, Step.mv 27 22, Step.rw 10 13 1 true, Step.rw 0 24 0 true, Step.mv 31 11, Step.mv 31 12,
     Step.mv 31 13, Step.mv 31 14, Step.mv 31 15, Step.mv 31 16, Step.mv 31 17, Step.rw 8 8 0 true, Step.mv 4 2, Step.mv 5 3,
     Step.mv 15 7, Step.rw 0 27 0 true, Step.mv 34 11, Step.mv 34 12, Step.mv 34 13, Step.mv 34 14, Step.mv 34 15,
     Step.mv 34 16, Step.mv 34 17, Step.rw 5 4 0 true, Step.mv 23 17, Step.mv 23 18, Step.mv 23 19, Step.mv 23 20,
     Step.mv 23 21, Step.mv 23 22, Step.rw 11 12 1 true, Step.rw 1 6 1 true, Step.mv 14 9, Step.mv 15 11, Step.mv 16 13,
     Step.mv 17 14, Step.rw 13 7 0 true, Step.rw 1 14 0 true, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8,
     Step.mv 16 12, Step.mv 17 14, Step.rw 15 9 0 true, Step.mv 9 5, Step.mv 10 6, Step.mv 11 7, Step.rw 2 13 0 true,
     Step.rw 4 12 0 true, Step.mv 12 8, Step.rw 4 13 0 true, Step.mv 13 9, Step.rw 4 14 0 true, Step.mv 14 10,
     Step.mv 19 11, Step.rw 7 7 0 true, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.rw 14 0 0 true,
     Step.mv 3 2, Step.rw 3 1 0 true, Step.mv 4 3, Step.mv 10 8])
    (by decide +kernel)

/-- Equation 3.35 (supplement: `[S 1 B 4 0 1]·ω^0 = [B 4 0 1 H 1 ZZ 0 1 S 0 S 1 H 1]·ω^0`). -/
theorem rule_3_35 :
    Holds 2 ([Lt.S 0] ++ bB 4 0)
      (bB 4 0 ++ [.H 0, .CZ 0, .S 1, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL7 (db_ok_cons hM15 db_ok_nil)))))))
    (steps := [Step.mv 4 3, Step.mv 1 0, Step.rw 3 1 0 false, Step.rw 2 6 1 true, Step.rw 1 6 0 true, Step.rw 2 7 0 true,
     Step.rw 1 9 0 true, Step.rw 0 18 0 true, Step.mv 25 10, Step.mv 25 11, Step.rw 5 6 0 true, Step.mv 4 2,
     Step.mv 16 7, Step.mv 17 9, Step.rw 0 26 0 true, Step.mv 33 13, Step.mv 33 14, Step.mv 33 15, Step.mv 33 16,
     Step.mv 33 17, Step.mv 33 18, Step.mv 33 19, Step.rw 6 3 0 true, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 5 3,
     Step.mv 12 7, Step.mv 20 11, Step.mv 20 12, Step.mv 20 13, Step.mv 20 14, Step.mv 20 15, Step.mv 20 16, Step.mv 20 17,
     Step.rw 4 4 0 true, Step.mv 3 2, Step.mv 9 7])
    (by decide +kernel)

/-- Equation 3.36 (supplement: `[X 1 B 1 0 1]·ω^0 = [B 1 0 1 X 0]·ω^0`). -/
theorem rule_3_36 :
    Holds 2 (bX 0 ++ bB 1 0)
      (bB 1 0 ++ bX 1) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hL14 (db_ok_cons hM14 db_ok_nil)))))
    (steps := [Step.mv 10 9, Step.rw 0 3 0 false, Step.rw 2 2 0 false, Step.rw 2 1 0 false, Step.mv 5 2, Step.rw 4 3 0 false,
     Step.mv 3 2, Step.mv 7 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.rw 0 8 0 false, Step.mv 8 7, Step.mv 9 8,
     Step.mv 10 9, Step.rw 2 10 0 false, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.rw 2 9 0 false, Step.rw 3 6 0 false,
     Step.mv 9 8, Step.mv 11 9, Step.mv 14 10, Step.mv 15 11, Step.rw 1 8 0 false, Step.mv 6 5])
    (by decide +kernel)

/-- Equation 3.37 (supplement: `[X 1 B 2 0 1]·ω^0 = [B 2 0 1 X 0]·ω^0`). -/
theorem rule_3_37 :
    Holds 2 (bX 0 ++ bB 2 0)
      (bB 2 0 ++ bX 1) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hL14 (db_ok_cons hM14 db_ok_nil)))))
    (steps := [Step.mv 6 5, Step.rw 4 1 0 false, Step.mv 5 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.rw 0 0 0 false,
     Step.rw 0 4 0 false, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.rw 2 6 0 false, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4,
     Step.rw 2 5 0 false, Step.rw 3 2 0 false, Step.mv 5 4, Step.mv 7 5, Step.mv 10 6, Step.mv 11 7, Step.rw 1 4 0 false,
     Step.mv 2 1])
    (by decide +kernel)

/-- Equation 3.38 (supplement: `[X 1 B 3 0 1]·ω^0 = [B 3 0 1 X 0]·ω^0`). -/
theorem rule_3_38 :
    Holds 2 (bX 0 ++ bB 3 0)
      (bB 3 0 ++ bX 1) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hL14 (db_ok_cons hM14 db_ok_nil))))))
    (steps := [Step.mv 8 7, Step.mv 4 1, Step.mv 5 2, Step.rw 5 3 0 false, Step.mv 3 1, Step.mv 7 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9,
     Step.rw 0 0 0 false, Step.rw 0 6 0 false, Step.rw 2 1 0 false, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 5 4,
     Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.rw 3 8 0 false, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6,
     Step.rw 3 7 0 false, Step.rw 4 4 0 false, Step.mv 7 6, Step.mv 9 7, Step.mv 12 8, Step.mv 13 9, Step.rw 1 6 0 false,
     Step.mv 3 2, Step.rw 2 1 0 true, Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.39 (supplement: `[X 1 B 4 0 1]·ω^0 = [B 4 0 1 X 0]·ω^0`). -/
theorem rule_3_39 :
    Holds 2 (bX 0 ++ bB 4 0)
      (bB 4 0 ++ bX 1) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hL14 (db_ok_cons hM14 db_ok_nil)))))
    (steps := [Step.mv 7 6, Step.mv 4 1, Step.rw 4 2 0 false, Step.mv 2 1, Step.mv 6 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8,
     Step.rw 0 0 0 false, Step.rw 0 5 0 false, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.rw 2 7 0 false, Step.mv 4 3,
     Step.mv 5 4, Step.mv 6 5, Step.rw 2 6 0 false, Step.rw 3 3 0 false, Step.mv 6 5, Step.mv 8 6, Step.mv 11 7,
     Step.mv 12 8, Step.rw 1 5 0 false, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.40 (supplement: `[ZZ 1 2 B 1 0 1]·ω^0 = [B 1 0 1 ZZ 0 1 H 1 ZZ 1 2 H 1 ZZ 0 1 H 1 ZZ 1 2 H 1]·ω^0`). -/
theorem rule_3_40 :
    Holds 3 ([Lt.CZ 0] ++ bB 1 1)
      (bB 1 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1, .H 1, .CZ 0, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 7 6, Step.mv 4 3, Step.mv 7 6, Step.rw 15 1 1 false, Step.mv 3 2, Step.mv 6 5, Step.rw 1 8 1 true, Step.mv 9 10,
     Step.rw 3 9 0 true, Step.mv 10 11, Step.rw 1 10 1 true, Step.mv 11 12, Step.rw 3 12 1 true, Step.rw 1 0 1 true,
     Step.rw 3 1 1 true, Step.rw 1 2 1 true, Step.rw 7 6 0 false, Step.rw 6 4 1 false, Step.mv 17 33, Step.mv 16 32,
     Step.mv 15 31, Step.mv 14 30, Step.mv 13 29, Step.mv 12 28, Step.mv 11 27, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.mv 11 10, Step.mv 12 11, Step.rw 13 3 1 false, Step.mv 19 39, Step.mv 18 38, Step.mv 17 37, Step.mv 16 36,
     Step.mv 15 35, Step.mv 14 34, Step.mv 13 33, Step.rw 0 39 0 false, Step.mv 8 7, Step.mv 10 8, Step.mv 11 9,
     Step.mv 12 10, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.mv 16 14, Step.mv 17 15, Step.rw 8 6 1 false,
     Step.mv 11 32, Step.mv 10 31, Step.rw 0 31 0 false, Step.rw 1 9 1 false, Step.rw 4 9 0 false,
     Step.rw 4 8 0 false, Step.rw 4 7 0 false, Step.mv 12 9, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12,
     Step.rw 12 13 1 false, Step.mv 13 9, Step.mv 17 16, Step.mv 19 17, Step.mv 20 18, Step.mv 21 19,
     Step.rw 1 18 1 false, Step.rw 10 11 1 false, Step.mv 14 13, Step.mv 16 14, Step.mv 19 15, Step.mv 20 16,
     Step.mv 21 17, Step.rw 9 19 2 false, Step.mv 28 38, Step.mv 27 37, Step.mv 26 36, Step.mv 25 35, Step.mv 18 13,
     Step.mv 19 14, Step.rw 1 13 2 false, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21,
     Step.rw 5 22 1 false, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20,
     Step.rw 5 21 1 false, Step.mv 16 13, Step.mv 17 14, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17,
     Step.rw 12 18 1 false, Step.mv 18 13, Step.mv 22 21, Step.mv 24 22, Step.mv 25 23, Step.mv 26 24, Step.mv 27 25,
     Step.mv 28 26, Step.mv 29 27, Step.mv 30 28, Step.rw 9 21 1 false, Step.mv 30 40, Step.mv 29 39, Step.mv 28 38,
     Step.mv 27 37, Step.rw 0 37 0 false, Step.rw 1 20 1 false, Step.rw 4 18 1 false, Step.mv 20 19, Step.mv 21 20,
     Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.rw 4 17 1 false, Step.mv 19 18,
     Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 25 18, Step.mv 26 19,
     Step.mv 27 20, Step.mv 28 21, Step.rw 2 18 2 false, Step.rw 10 14 1 false, Step.mv 17 16, Step.mv 19 17,
     Step.mv 22 18, Step.mv 23 19, Step.mv 24 20, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24,
     Step.rw 2 16 1 false, Step.rw 1 24 2 false, Step.mv 10 8, Step.mv 11 9, Step.mv 14 13, Step.rw 14 10 1 false,
     Step.mv 10 8, Step.mv 13 12, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19,
     Step.rw 1 22 2 false, Step.rw 11 9 1 false, Step.rw 1 16 1 false, Step.rw 4 17 0 false,
     Step.rw 4 16 0 false, Step.rw 4 15 0 false, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20,
     Step.rw 12 21 1 false, Step.mv 21 17, Step.mv 25 24, Step.mv 27 25, Step.mv 28 26, Step.rw 4 21 1 false,
     Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.rw 4 20 1 false, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23, Step.mv 25 24, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.rw 2 21 2 false,
     Step.rw 4 19 1 false, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 9 7, Step.mv 18 15,
     Step.rw 16 5 0 false, Step.mv 10 9, Step.mv 12 10, Step.mv 15 11, Step.mv 16 12, Step.mv 17 13, Step.mv 18 14,
     Step.rw 1 4 1 false, Step.rw 1 8 1 false, Step.rw 2 12 2 false, Step.mv 4 3, Step.rw 5 4 1 false,
     Step.rw 4 5 0 false, Step.rw 2 6 1 false, Step.rw 1 5 1 true, Step.mv 9 6, Step.rw 3 7 1 true, Step.mv 6 5])
    (by decide +kernel)

end QCert.SelingerClifford
