/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): rewrite rules, part 5

Equations 3.81–3.101 of the supplement to Selinger's paper (the rewrite
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

/-- Equation 3.81 (supplement: `[ZZ 0 1 D 4 0 1]·ω^0 = [D 1 0 1]·ω^0`). -/
theorem rule_3_81 :
    Holds 2 ([Lt.CZ 0] ++ bD 4 0)
      (bD 1 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [Step.mv 2 1, Step.mv 5 4, Step.mv 2 1, Step.mv 5 4])
    (by decide +kernel)

/-- Equation 3.82 (supplement: `[S 0 E 1 0]·ω^0 = [E 2 0]·ω^0`). -/
theorem rule_3_82 :
    Holds 1 ([Lt.S 0] ++ bE 1 0)
      (bE 2 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.83 (supplement: `[S 0 E 2 0]·ω^0 = [E 3 0]·ω^0`). -/
theorem rule_3_83 :
    Holds 1 ([Lt.S 0] ++ bE 2 0)
      (bE 3 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.84 (supplement: `[S 0 E 3 0]·ω^0 = [E 4 0]·ω^0`). -/
theorem rule_3_84 :
    Holds 1 ([Lt.S 0] ++ bE 3 0)
      (bE 4 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.85 (supplement: `[S 0 E 4 0]·ω^0 = [E 1 0]·ω^0`). -/
theorem rule_3_85 :
    Holds 1 ([Lt.S 0] ++ bE 4 0)
      (bE 1 0) :=
  Holds.of_derives (db_ok_cons hC3 db_ok_nil)
    (steps := [Step.rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.86 (supplement: `[ZZ 1 2 D 1 0 1 D 1 1 2]·ω^0 = [D 1 0 1 D 1 1 2 H 0 H 1 ZZ 0 1 H 0 H 1]·ω^0`). -/
theorem rule_3_86 :
    Holds 3 ([Lt.CZ 0] ++ bD 1 1 ++ bD 1 0)
      (bD 1 1 ++ bD 1 0 ++ [.H 2, .H 1, .CZ 1, .H 2, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hL18 (db_ok_cons hL20 (db_ok_cons hM16 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.mv 11 10, Step.mv 14 13, Step.rw 15 8 0 false, Step.rw 1 15 0 false, Step.rw 1 1 0 true,
     Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.rw 3 9 0 true,
     Step.rw 1 10 1 true, Step.rw 1 10 0 true, Step.mv 12 11, Step.rw 3 12 0 true, Step.rw 1 25 2 true,
     Step.rw 1 13 1 true, Step.rw 1 3 1 true, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 6 4, Step.mv 6 5, Step.mv 9 8,
     Step.mv 29 11, Step.mv 14 13, Step.rw 16 5 0 true, Step.mv 5 4, Step.mv 7 5, Step.mv 7 6, Step.mv 10 9, Step.mv 13 12,
     Step.mv 15 13, Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.rw 2 17 1 true, Step.rw 1 18 1 true, Step.mv 6 5,
     Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 14 13, Step.rw 17 11 0 true, Step.mv 11 5,
     Step.mv 12 6, Step.mv 15 14, Step.rw 1 20 1 true, Step.rw 2 17 0 true, Step.mv 21 17, Step.mv 22 19, Step.mv 23 21,
     Step.mv 24 22, Step.rw 12 15 0 true, Step.rw 4 18 0 true, Step.mv 18 15, Step.rw 4 19 0 true, Step.mv 19 16,
     Step.rw 2 21 0 true, Step.rw 4 20 0 true, Step.mv 20 17, Step.rw 0 43 0 true, Step.mv 50 18,
     Step.rw 9 14 0 true, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.mv 18 14,
     Step.mv 49 18, Step.mv 49 19, Step.mv 49 20, Step.mv 49 21, Step.mv 49 22, Step.mv 49 23, Step.mv 49 24,
     Step.rw 6 11 0 true, Step.rw 2 22 1 true, Step.rw 1 24 1 true, Step.rw 1 21 0 true, Step.rw 0 47 0 true,
     Step.mv 54 22, Step.rw 8 18 0 true, Step.mv 53 21, Step.mv 53 22, Step.mv 53 23, Step.mv 53 24, Step.mv 53 25,
     Step.mv 53 26, Step.mv 53 27, Step.rw 11 18 0 true, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26,
     Step.rw 14 13 0 true, Step.rw 1 26 1 true, Step.rw 0 45 0 true, Step.mv 52 27, Step.mv 52 28,
     Step.rw 10 23 1 true, Step.mv 23 19, Step.mv 24 21, Step.mv 25 23, Step.mv 26 24, Step.mv 27 25,
     Step.rw 0 53 0 true, Step.mv 60 26, Step.mv 60 27, Step.mv 60 28, Step.mv 60 29, Step.mv 60 30, Step.mv 60 31,
     Step.mv 60 32, Step.rw 13 16 0 true, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 47 24, Step.mv 47 25,
     Step.mv 47 26, Step.mv 47 27, Step.mv 47 28, Step.mv 47 29, Step.mv 47 30, Step.rw 5 17 0 true, Step.mv 21 19,
     Step.mv 22 21, Step.rw 7 20 0 false, Step.rw 15 21 0 true, Step.rw 1 6 2 true, Step.mv 6 4, Step.mv 7 5,
     Step.rw 3 6 1 true, Step.rw 7 7 0 true, Step.rw 1 2 1 false, Step.rw 1 2 2 false, Step.rw 3 1 1 false,
     Step.rw 3 0 0 false, Step.rw 3 24 0 false, Step.mv 24 23, Step.rw 1 22 0 false, Step.rw 1 22 1 false,
     Step.rw 3 21 0 false, Step.mv 21 20, Step.rw 1 19 0 false, Step.rw 1 19 1 false, Step.rw 3 18 0 false,
     Step.rw 1 14 0 true, Step.rw 15 7 0 true, Step.mv 2 1, Step.mv 5 4, Step.mv 10 9, Step.mv 13 12, Step.mv 17 16,
     Step.mv 20 19])
    (by decide +kernel)

/-- Equation 3.87 (supplement: `[ZZ 1 2 D 1 0 1 D 2 1 2]·ω^0 = [D 4 0 1 D 2 1 2 H 0 ZZ 0 1 H 0]·ω^0`). -/
theorem rule_3_87 :
    Holds 3 ([Lt.CZ 0] ++ bD 1 1 ++ bD 2 0)
      (bD 4 1 ++ bD 2 0 ++ [.H 2, .CZ 1, .H 2]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.mv 12 11, Step.rw 1 8 1 false, Step.rw 1 12 2 true, Step.mv 13 14, Step.rw 3 13 1 true,
     Step.mv 14 15, Step.rw 1 15 2 true, Step.rw 3 14 0 true, Step.rw 1 15 1 true, Step.rw 1 15 0 true,
     Step.rw 1 12 0 true, Step.rw 1 0 2 true, Step.mv 1 2, Step.rw 1 0 1 true, Step.mv 1 2, Step.rw 3 2 1 true,
     Step.rw 1 3 1 true, Step.rw 1 20 0 false, Step.rw 12 8 1 false, Step.rw 7 7 0 false, Step.rw 6 5 1 false,
     Step.mv 18 43, Step.mv 17 42, Step.mv 16 41, Step.mv 15 40, Step.mv 14 39, Step.mv 13 38, Step.mv 12 37, Step.mv 9 8,
     Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.rw 14 4 1 false, Step.mv 20 49, Step.mv 19 48,
     Step.mv 18 47, Step.mv 17 46, Step.mv 16 45, Step.mv 15 44, Step.mv 14 43, Step.rw 0 49 0 false, Step.mv 9 8,
     Step.mv 11 9, Step.mv 12 10, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.mv 16 14, Step.mv 17 15, Step.mv 18 16,
     Step.rw 8 7 1 false, Step.mv 12 42, Step.mv 11 41, Step.rw 0 41 0 false, Step.rw 1 10 1 false,
     Step.rw 4 10 0 false, Step.rw 4 9 0 false, Step.rw 4 8 0 false, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12,
     Step.mv 16 13, Step.rw 13 14 1 false, Step.mv 14 10, Step.mv 18 17, Step.mv 20 18, Step.mv 21 19, Step.mv 22 20,
     Step.rw 1 19 1 false, Step.rw 10 12 1 false, Step.mv 15 14, Step.mv 17 15, Step.mv 20 16, Step.mv 21 17,
     Step.mv 22 18, Step.rw 9 20 2 false, Step.mv 29 48, Step.mv 28 47, Step.mv 27 46, Step.mv 26 45, Step.mv 19 14,
     Step.mv 20 15, Step.rw 1 14 2 false, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22,
     Step.rw 5 23 1 false, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21,
     Step.rw 5 22 1 false, Step.mv 17 14, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18,
     Step.rw 13 19 1 false, Step.mv 19 14, Step.mv 23 22, Step.mv 25 23, Step.mv 26 24, Step.mv 27 25, Step.mv 28 26,
     Step.mv 29 27, Step.mv 30 28, Step.mv 31 29, Step.mv 32 30, Step.mv 33 31, Step.rw 9 22 1 false, Step.mv 31 50,
     Step.mv 30 49, Step.mv 29 48, Step.mv 28 47, Step.rw 0 47 0 false, Step.rw 1 21 1 false, Step.rw 4 19 1 false,
     Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27,
     Step.mv 29 28, Step.rw 4 18 1 false, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23,
     Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 28 19, Step.mv 29 20, Step.mv 30 21, Step.mv 31 22,
     Step.rw 2 19 2 false, Step.rw 10 15 1 false, Step.mv 18 17, Step.mv 20 18, Step.mv 23 19, Step.mv 24 20,
     Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26, Step.mv 31 27,
     Step.rw 2 17 1 false, Step.rw 1 27 2 false, Step.mv 11 9, Step.mv 12 10, Step.mv 15 14, Step.rw 15 11 1 false,
     Step.mv 11 9, Step.mv 14 13, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20, Step.mv 24 21,
     Step.mv 25 22, Step.rw 1 25 2 false, Step.rw 11 10 1 false, Step.rw 1 17 1 false, Step.rw 4 18 0 false,
     Step.mv 20 19, Step.rw 4 17 0 false, Step.mv 19 18, Step.rw 4 16 0 false, Step.mv 18 17, Step.rw 7 27 0 true,
     Step.mv 27 23, Step.mv 29 24, Step.mv 30 25, Step.rw 3 22 0 false, Step.mv 22 18, Step.mv 23 19,
     Step.rw 1 17 0 false, Step.mv 22 19, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22, Step.rw 13 23 1 false,
     Step.mv 23 19, Step.mv 27 26, Step.mv 29 27, Step.mv 30 28, Step.mv 31 29, Step.mv 32 30, Step.mv 33 31, Step.mv 34 32,
     Step.rw 1 28 1 false, Step.rw 4 23 1 false, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27,
     Step.mv 29 28, Step.mv 30 29, Step.rw 4 22 1 false, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26,
     Step.mv 28 27, Step.mv 29 28, Step.mv 29 23, Step.mv 30 24, Step.mv 31 25, Step.mv 32 26, Step.rw 2 23 2 false,
     Step.rw 4 21 1 false, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27,
     Step.mv 10 8, Step.mv 20 16, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.rw 16 6 0 false, Step.mv 16 10,
     Step.mv 12 11, Step.mv 14 12, Step.mv 17 13, Step.mv 18 14, Step.mv 19 15, Step.mv 20 16, Step.mv 21 17, Step.mv 22 18,
     Step.rw 1 5 1 false, Step.rw 1 10 1 false, Step.rw 2 16 2 false, Step.mv 15 7, Step.mv 16 8,
     Step.rw 1 7 2 false, Step.mv 5 4, Step.rw 5 5 1 false, Step.rw 4 6 0 false, Step.mv 8 7, Step.mv 8 7, Step.mv 9 8,
     Step.mv 10 9, Step.mv 11 10, Step.rw 2 7 1 false, Step.rw 1 6 1 true, Step.mv 1 0, Step.mv 4 3, Step.mv 10 9])
    (by decide +kernel)

/-- Equation 3.88 (supplement: `[ZZ 1 2 D 1 0 1 D 3 1 2]·ω^0 = [D 4 0 1 D 3 1 2 H 0 H 1 S 1 H 1 ZZ 0 1 H 0 S 1 H 1 S 1]·ω^7`). -/
theorem rule_3_88 :
    Holds 3 ([Lt.CZ 0] ++ bD 1 1 ++ bD 3 0)
      (bD 4 1 ++ bD 3 0 ++ [.H 2, .H 1, .S 1, .H 1, .CZ 1, .H 2, .S 1, .H 1, .S 1, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM17 (db_ok_cons hM21 db_ok_nil)))))))))))))))))))))
    (steps := [Step.mv 10 1, Step.mv 11 2, Step.mv 5 4, Step.mv 8 7, Step.mv 14 13, Step.rw 1 10 1 false, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4,
     Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.rw 5 9 0 false, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4,
     Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 12 10, Step.rw 19 8 0 false, Step.mv 10 9, Step.mv 11 10, Step.mv 18 13,
     Step.mv 19 14, Step.mv 20 15, Step.mv 21 16, Step.mv 22 17, Step.rw 1 16 0 false, Step.rw 1 13 2 true,
     Step.mv 14 22, Step.rw 3 14 1 true, Step.mv 15 18, Step.rw 3 15 0 true, Step.rw 1 16 0 true,
     Step.rw 2 13 1 true, Step.rw 2 13 1 true, Step.rw 1 16 1 true, Step.rw 2 17 1 true, Step.rw 1 13 0 true,
     Step.rw 2 14 0 true, Step.rw 1 0 2 true, Step.mv 1 2, Step.rw 1 0 1 true, Step.mv 1 2, Step.rw 3 2 1 true,
     Step.rw 1 3 2 true, Step.rw 1 3 1 true, Step.rw 2 24 0 false, Step.rw 1 23 0 false, Step.rw 12 23 1 false,
     Step.mv 32 55, Step.mv 31 54, Step.mv 30 53, Step.mv 29 52, Step.mv 28 51, Step.mv 27 50, Step.mv 26 49,
     Step.rw 8 23 1 false, Step.mv 27 49, Step.rw 0 49 0 false, Step.rw 1 26 1 false, Step.rw 2 23 1 false,
     Step.rw 2 23 1 false, Step.rw 15 10 1 false, Step.rw 7 9 0 false, Step.rw 6 7 1 false, Step.mv 20 49,
     Step.mv 19 48, Step.mv 18 47, Step.mv 17 46, Step.mv 16 45, Step.mv 15 44, Step.mv 14 43, Step.mv 7 5, Step.mv 8 6,
     Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.mv 15 14, Step.mv 7 4, Step.mv 8 5,
     Step.rw 17 6 1 false, Step.mv 22 55, Step.mv 21 54, Step.mv 20 53, Step.mv 19 52, Step.mv 18 51, Step.mv 17 50,
     Step.mv 16 49, Step.rw 0 55 0 false, Step.mv 6 4, Step.mv 7 5, Step.mv 11 10, Step.mv 13 11, Step.mv 14 12,
     Step.mv 15 13, Step.mv 16 14, Step.mv 17 15, Step.mv 18 16, Step.mv 19 17, Step.mv 20 18, Step.rw 10 9 1 false,
     Step.mv 14 48, Step.mv 13 47, Step.rw 0 47 0 false, Step.rw 1 12 1 false, Step.rw 4 12 0 false,
     Step.rw 4 11 0 false, Step.rw 4 10 0 false, Step.mv 15 12, Step.mv 16 13, Step.mv 17 14, Step.mv 18 15,
     Step.rw 16 16 1 false, Step.mv 16 12, Step.mv 20 19, Step.mv 22 20, Step.mv 23 21, Step.mv 24 22,
     Step.rw 1 21 1 false, Step.rw 13 14 1 false, Step.mv 17 16, Step.mv 19 17, Step.mv 22 18, Step.mv 23 19,
     Step.mv 24 20, Step.rw 11 22 2 false, Step.mv 31 54, Step.mv 30 53, Step.mv 29 52, Step.mv 28 51, Step.mv 21 16,
     Step.mv 22 17, Step.rw 1 16 2 false, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24,
     Step.rw 5 25 1 false, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23,
     Step.rw 5 24 1 false, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20,
     Step.rw 16 21 1 false, Step.mv 21 16, Step.mv 25 24, Step.mv 27 25, Step.mv 28 26, Step.mv 29 27, Step.mv 30 28,
     Step.mv 31 29, Step.mv 32 30, Step.mv 33 31, Step.mv 34 32, Step.mv 35 33, Step.mv 36 34, Step.rw 11 24 1 false,
     Step.mv 33 56, Step.mv 32 55, Step.mv 31 54, Step.mv 30 53, Step.rw 0 53 0 false, Step.rw 1 23 1 false,
     Step.rw 4 21 1 false, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27,
     Step.mv 29 28, Step.mv 30 29, Step.mv 31 30, Step.mv 32 31, Step.rw 4 20 1 false, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29, Step.mv 31 30,
     Step.mv 31 21, Step.mv 32 22, Step.mv 33 23, Step.mv 34 24, Step.rw 2 21 2 false, Step.rw 13 17 1 false,
     Step.mv 20 19, Step.mv 22 20, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26,
     Step.mv 31 27, Step.mv 32 28, Step.mv 33 29, Step.mv 34 30, Step.rw 2 19 1 false, Step.rw 1 30 2 false,
     Step.mv 13 11, Step.mv 14 12, Step.mv 17 16, Step.rw 18 13 1 false, Step.mv 13 11, Step.mv 16 15, Step.mv 21 18,
     Step.mv 22 19, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22, Step.mv 26 23, Step.mv 27 24, Step.mv 28 25,
     Step.rw 1 28 2 false, Step.rw 14 12 1 false, Step.rw 1 19 1 false, Step.rw 4 20 0 false, Step.mv 22 21,
     Step.mv 23 22, Step.rw 4 19 0 false, Step.mv 21 20, Step.mv 22 21, Step.rw 4 18 0 false, Step.mv 20 19,
     Step.mv 21 20, Step.rw 7 30 0 true, Step.mv 30 26, Step.mv 32 27, Step.mv 33 28, Step.rw 3 25 0 false,
     Step.mv 25 21, Step.mv 26 22, Step.rw 1 20 0 false, Step.mv 25 22, Step.mv 26 23, Step.mv 27 24, Step.mv 28 25,
     Step.rw 16 26 1 false, Step.mv 26 22, Step.mv 30 29, Step.mv 32 30, Step.mv 33 31, Step.mv 34 32, Step.mv 35 33,
     Step.mv 36 34, Step.mv 37 35, Step.rw 4 26 1 false, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29, Step.mv 31 30,
     Step.mv 32 31, Step.mv 33 32, Step.mv 34 33, Step.mv 35 34, Step.rw 4 25 1 false, Step.mv 27 26, Step.mv 28 27,
     Step.mv 29 28, Step.mv 30 29, Step.mv 31 30, Step.mv 32 31, Step.mv 33 32, Step.mv 34 33, Step.mv 34 26, Step.mv 35 27,
     Step.mv 36 28, Step.mv 37 29, Step.rw 2 26 2 false, Step.rw 4 24 1 false, Step.mv 26 25, Step.mv 27 26,
     Step.mv 28 27, Step.mv 29 28, Step.mv 30 29, Step.mv 31 30, Step.mv 32 31, Step.mv 33 32, Step.mv 12 10, Step.mv 23 18,
     Step.mv 22 20, Step.mv 23 21, Step.mv 24 22, Step.rw 20 8 0 false, Step.mv 8 6, Step.mv 18 12, Step.mv 19 13,
     Step.mv 15 14, Step.mv 17 15, Step.mv 20 16, Step.mv 21 17, Step.mv 22 18, Step.mv 23 19, Step.mv 24 20, Step.mv 25 21,
     Step.mv 26 22, Step.mv 27 23, Step.rw 1 5 1 false, Step.mv 5 3, Step.mv 6 4, Step.rw 1 3 2 false,
     Step.rw 1 11 1 false, Step.rw 2 19 2 false, Step.mv 5 4, Step.rw 5 5 1 false, Step.rw 4 6 0 false, Step.mv 8 7,
     Step.mv 9 8, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.rw 2 7 1 false, Step.rw 5 15 1 true,
     Step.mv 15 14, Step.rw 5 16 1 true, Step.mv 16 15, Step.rw 1 16 1 true, Step.rw 2 17 1 true,
     Step.rw 0 28 0 true, Step.mv 35 20, Step.rw 9 16 1 true, Step.rw 1 14 0 true, Step.mv 9 7, Step.mv 16 11,
     Step.mv 17 12, Step.mv 18 13, Step.mv 19 14, Step.mv 20 15, Step.rw 19 6 0 true, Step.mv 6 0, Step.mv 9 8, Step.mv 10 9,
     Step.rw 5 7 0 true, Step.mv 7 1, Step.rw 1 8 1 true, Step.mv 3 0, Step.mv 3 1, Step.mv 4 2, Step.mv 6 3, Step.mv 6 4,
     Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 12 11, Step.mv 18 15, Step.mv 23 20])
    (by decide +kernel)

/-- Equation 3.89 (supplement: `[ZZ 1 2 D 1 0 1 D 4 1 2]·ω^0 = [D 1 0 1 D 4 1 2 H 0 H 1 ZZ 0 1 H 0 H 1]·ω^0`). -/
theorem rule_3_89 :
    Holds 3 ([Lt.CZ 0] ++ bD 1 1 ++ bD 4 0)
      (bD 1 1 ++ bD 4 0 ++ [.H 2, .H 1, .CZ 1, .H 2, .H 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC12 (db_ok_cons hL20 db_ok_nil))))
    (steps := [Step.mv 10 1, Step.mv 4 3, Step.mv 7 6, Step.mv 13 12, Step.rw 0 9 1 false, Step.rw 0 14 2 true, Step.rw 0 14 1 true,
     Step.rw 0 3 1 true, Step.rw 0 1 0 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 8 6, Step.mv 8 7, Step.mv 11 10,
     Step.mv 20 13, Step.mv 16 15, Step.mv 19 18, Step.rw 3 7 0 true, Step.mv 7 6, Step.mv 9 7, Step.mv 9 8, Step.mv 12 11,
     Step.mv 15 14, Step.mv 17 15, Step.mv 17 16, Step.mv 18 17, Step.mv 21 18, Step.mv 20 19, Step.rw 0 9 2 true,
     Step.mv 9 6, Step.mv 10 7, Step.rw 1 8 1 true, Step.rw 2 9 0 true, Step.mv 11 10, Step.rw 0 22 0 true,
     Step.rw 0 1 0 false, Step.rw 0 2 1 false, Step.rw 0 2 2 false, Step.rw 1 1 1 false, Step.rw 1 0 0 false,
     Step.rw 0 12 0 false, Step.rw 0 8 1 true, Step.mv 1 0, Step.mv 3 1, Step.mv 3 2, Step.mv 4 3, Step.mv 6 4, Step.mv 6 5,
     Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 12 11, Step.mv 16 15, Step.mv 19 18])
    (by decide +kernel)

/-- Equation 3.90 (supplement: `[ZZ 1 2 D 2 0 1 D 1 1 2]·ω^0 = [D 2 0 1 D 4 1 2 H 1 ZZ 0 1 H 1]·ω^0`). -/
theorem rule_3_90 :
    Holds 3 ([Lt.CZ 0] ++ bD 2 1 ++ bD 1 0)
      (bD 2 1 ++ bD 4 0 ++ [.H 1, .CZ 1, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 4 3, Step.mv 9 8, Step.mv 12 11, Step.rw 14 6 0 false, Step.rw 1 13 0 false, Step.rw 1 13 1 true,
     Step.rw 3 14 1 true, Step.rw 1 15 1 true, Step.rw 1 13 0 true, Step.mv 14 17, Step.rw 3 17 0 true,
     Step.rw 1 0 2 true, Step.mv 1 2, Step.rw 3 1 1 true, Step.rw 1 2 2 true, Step.rw 1 2 1 true, Step.mv 3 4,
     Step.rw 3 4 1 true, Step.rw 1 0 0 true, Step.mv 12 11, Step.mv 13 12, Step.rw 1 11 2 false,
     Step.rw 7 11 0 false, Step.rw 3 10 1 false, Step.mv 10 9, Step.mv 11 10, Step.mv 11 8, Step.mv 12 9,
     Step.rw 1 8 2 false, Step.rw 7 11 0 true, Step.mv 13 12, Step.rw 6 9 0 false, Step.mv 22 39, Step.mv 21 38,
     Step.mv 20 37, Step.mv 19 36, Step.mv 18 35, Step.mv 17 34, Step.mv 16 33, Step.mv 16 13, Step.rw 12 8 0 false,
     Step.mv 24 45, Step.mv 23 44, Step.mv 22 43, Step.mv 21 42, Step.mv 20 41, Step.mv 19 40, Step.mv 18 39,
     Step.rw 0 45 0 false, Step.mv 12 11, Step.mv 14 12, Step.mv 18 13, Step.mv 19 14, Step.rw 9 15 1 false,
     Step.mv 20 38, Step.mv 19 37, Step.rw 0 37 0 false, Step.rw 1 18 1 false, Step.rw 5 18 1 false,
     Step.rw 13 19 0 false, Step.rw 1 26 0 false, Step.rw 5 17 1 false, Step.rw 13 18 0 false,
     Step.rw 1 25 0 false, Step.rw 5 16 1 false, Step.rw 13 17 0 false, Step.rw 1 24 0 false, Step.mv 15 12,
     Step.mv 16 13, Step.mv 17 14, Step.rw 16 15 0 false, Step.mv 15 12, Step.mv 19 18, Step.mv 21 19, Step.mv 22 20,
     Step.mv 23 21, Step.rw 1 20 0 false, Step.rw 11 20 0 false, Step.mv 23 22, Step.mv 25 23, Step.mv 28 24,
     Step.mv 29 25, Step.mv 30 26, Step.mv 31 27, Step.rw 1 31 1 false, Step.mv 20 19, Step.rw 5 20 0 false,
     Step.rw 10 21 0 false, Step.mv 30 41, Step.mv 29 40, Step.mv 28 39, Step.mv 27 38, Step.mv 26 37, Step.mv 25 36,
     Step.mv 24 35, Step.mv 19 18, Step.rw 5 19 0 false, Step.rw 8 20 0 false, Step.mv 24 35, Step.rw 0 35 0 false,
     Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.mv 18 17, Step.rw 17 14 0 false, Step.mv 14 11, Step.mv 17 16,
     Step.mv 22 19, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22, Step.rw 1 25 1 false, Step.rw 5 26 1 false,
     Step.rw 5 25 1 false, Step.rw 11 26 0 false, Step.mv 29 28, Step.mv 31 29, Step.rw 5 24 1 false, Step.mv 23 22,
     Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.rw 5 26 0 false, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23,
     Step.mv 25 24, Step.rw 5 25 0 false, Step.rw 2 26 0 false, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23, Step.rw 5 24 0 false, Step.mv 12 11, Step.mv 17 16, Step.mv 20 19, Step.rw 15 10 0 false,
     Step.mv 11 2, Step.mv 14 13, Step.mv 16 14, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.rw 1 0 0 false,
     Step.rw 1 8 1 false, Step.rw 2 10 0 false, Step.rw 1 12 1 false, Step.rw 4 7 0 false, Step.mv 9 8,
     Step.rw 5 9 1 false, Step.rw 2 10 1 false, Step.mv 9 8, Step.rw 7 7 0 false, Step.rw 3 5 1 false,
     Step.rw 1 6 1 true, Step.mv 1 0, Step.mv 2 1, Step.mv 4 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 10 9])
    (by decide +kernel)

/-- Equation 3.91 (supplement: `[ZZ 1 2 D 2 0 1 D 2 1 2]·ω^0 = [D 3 0 1 D 3 1 2 H 0 S 0 H 0 H 1 S 1 H 1 ZZ 0 1 S 0 S 1]·ω^6`). -/
theorem rule_3_91 :
    Holds 3 ([Lt.CZ 0] ++ bD 2 1 ++ bD 2 0)
      (bD 3 1 ++ bD 3 0 ++ [.H 2, .S 2, .H 2, .H 1, .S 1, .H 1, .CZ 1, .S 2, .S 1, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 4 3, Step.mv 10 9, Step.rw 1 6 1 false, Step.rw 3 9 1 true, Step.rw 8 10 0 true, Step.mv 12 11,
     Step.rw 2 13 2 true, Step.rw 4 12 1 true, Step.rw 2 14 1 true, Step.rw 5 13 1 true, Step.mv 13 12,
     Step.mv 12 11, Step.rw 4 10 0 true, Step.rw 2 13 2 true, Step.rw 1 10 1 true, Step.rw 2 11 1 true,
     Step.rw 1 13 1 true, Step.mv 21 11, Step.mv 22 13, Step.rw 14 8 1 true, Step.rw 0 29 0 true, Step.mv 36 16,
     Step.mv 36 17, Step.rw 11 12 1 true, Step.mv 21 12, Step.rw 0 37 0 true, Step.mv 44 16, Step.mv 44 17,
     Step.mv 44 18, Step.mv 44 19, Step.mv 44 20, Step.mv 44 21, Step.mv 44 22, Step.rw 7 9 1 true, Step.rw 5 8 1 false,
     Step.rw 1 16 1 true, Step.mv 20 13, Step.mv 21 15, Step.mv 35 19, Step.mv 35 20, Step.mv 35 21, Step.mv 35 22,
     Step.mv 35 23, Step.mv 35 24, Step.mv 35 25, Step.rw 15 9 1 true, Step.rw 3 6 0 true, Step.mv 10 9,
     Step.rw 8 8 0 false, Step.rw 0 25 0 true, Step.mv 32 14, Step.mv 32 15, Step.mv 32 16, Step.mv 32 17, Step.mv 32 18,
     Step.mv 32 19, Step.mv 32 20, Step.rw 12 11 1 true, Step.mv 29 15, Step.rw 9 11 1 true, Step.rw 0 29 0 true,
     Step.mv 36 17, Step.rw 10 13 1 true, Step.rw 2 10 0 true, Step.rw 1 9 1 true, Step.mv 17 12, Step.mv 18 14,
     Step.mv 19 16, Step.mv 20 17, Step.rw 13 10 0 true, Step.mv 17 15, Step.mv 18 16, Step.mv 19 17, Step.mv 37 18,
     Step.mv 37 19, Step.mv 37 20, Step.mv 37 21, Step.mv 37 22, Step.mv 37 23, Step.mv 37 24, Step.rw 6 11 0 true,
     Step.mv 16 14, Step.rw 8 13 0 false, Step.rw 4 10 0 false, Step.rw 1 13 2 true, Step.mv 13 10,
     Step.rw 3 11 1 true, Step.rw 8 12 0 true, Step.rw 1 13 2 true, Step.rw 3 6 0 false, Step.rw 3 5 1 false,
     Step.mv 5 4, Step.rw 1 3 1 false, Step.rw 1 3 2 false, Step.rw 3 2 1 false, Step.mv 2 1, Step.rw 3 0 0 false,
     Step.rw 1 0 2 false, Step.mv 16 13, Step.rw 4 12 1 true, Step.mv 17 14, Step.rw 4 13 1 true,
     Step.rw 5 14 1 true, Step.mv 14 12, Step.rw 5 15 1 true, Step.mv 15 13, Step.mv 12 11, Step.rw 4 10 0 true,
     Step.mv 13 12, Step.rw 4 11 0 true, Step.rw 2 14 1 true, Step.rw 2 14 0 true, Step.rw 1 16 0 true, Step.mv 9 8,
     Step.mv 10 9, Step.mv 11 10, Step.mv 20 14, Step.mv 21 16, Step.rw 14 11 0 true, Step.mv 11 8, Step.mv 12 9,
     Step.mv 13 10, Step.rw 1 14 1 true, Step.rw 1 6 1 true, Step.mv 13 9, Step.mv 14 11, Step.mv 15 13, Step.mv 16 14,
     Step.rw 13 7 0 true, Step.rw 1 20 1 true, Step.rw 2 21 1 true, Step.rw 0 31 0 true, Step.mv 38 24,
     Step.rw 10 20 1 true, Step.rw 1 18 0 true, Step.mv 13 11, Step.mv 20 15, Step.mv 21 16, Step.mv 22 17,
     Step.mv 23 18, Step.mv 24 19, Step.rw 16 10 0 true, Step.mv 10 0, Step.mv 13 12, Step.mv 14 13, Step.rw 5 11 0 true,
     Step.mv 11 1, Step.rw 1 22 2 true, Step.rw 2 23 2 true, Step.mv 37 26, Step.rw 10 22 2 true, Step.mv 6 4,
     Step.mv 20 8, Step.mv 21 9, Step.mv 22 10, Step.mv 23 11, Step.mv 24 12, Step.rw 16 3 1 true, Step.mv 3 2, Step.mv 6 5,
     Step.mv 7 6, Step.rw 5 4 1 true, Step.mv 4 3, Step.rw 1 9 1 true, Step.mv 4 0, Step.mv 3 1, Step.mv 4 2, Step.mv 5 3,
     Step.mv 7 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 13 12, Step.mv 19 16, Step.mv 20 17,
     Step.mv 21 18, Step.mv 24 23])
    (by decide +kernel)

/-- Equation 3.92 (supplement: `[ZZ 1 2 D 2 0 1 D 3 1 2]·ω^0 = [D 3 0 1 D 2 1 2 H 0 S 0 H 0 ZZ 0 1 S 0 H 1 S 1 S 2 S 2]·ω^7`). -/
theorem rule_3_92 :
    Holds 3 ([Lt.CZ 0] ++ bD 2 1 ++ bD 3 0)
      (bD 3 1 ++ bD 2 0 ++ [.H 2, .S 2, .H 2, .CZ 1, .S 2, .H 1, .S 1, .S 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 8 1, Step.mv 9 2, Step.mv 6 5, Step.mv 12 11, Step.rw 1 8 1 false, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5,
     Step.mv 7 6, Step.rw 5 7 0 false, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 10 8,
     Step.rw 16 6 0 false, Step.mv 8 7, Step.mv 9 8, Step.mv 16 11, Step.mv 17 12, Step.mv 18 13, Step.mv 19 14,
     Step.mv 20 15, Step.rw 1 14 0 false, Step.rw 3 14 1 true, Step.rw 3 10 0 true, Step.mv 16 13,
     Step.rw 8 12 0 false, Step.rw 2 23 2 true, Step.mv 23 18, Step.rw 4 17 1 true, Step.rw 5 18 1 true,
     Step.mv 18 17, Step.rw 5 19 1 true, Step.mv 19 18, Step.rw 5 20 1 true, Step.mv 20 19, Step.mv 17 14,
     Step.rw 4 13 0 true, Step.rw 1 18 0 true, Step.rw 1 12 0 true, Step.mv 14 13, Step.mv 15 14, Step.mv 22 18,
     Step.mv 23 20, Step.rw 14 15 0 true, Step.mv 15 13, Step.mv 16 14, Step.mv 17 15, Step.rw 2 20 2 true,
     Step.rw 1 17 1 true, Step.rw 2 18 1 true, Step.rw 1 20 1 true, Step.rw 1 16 1 true, Step.mv 30 20,
     Step.mv 31 22, Step.rw 14 17 1 true, Step.rw 0 37 0 true, Step.mv 44 25, Step.mv 44 26, Step.rw 11 21 1 true,
     Step.mv 30 21, Step.rw 0 45 0 true, Step.mv 52 25, Step.mv 52 26, Step.mv 52 27, Step.mv 52 28, Step.mv 52 29,
     Step.mv 52 30, Step.mv 52 31, Step.rw 7 18 1 true, Step.rw 5 17 1 false, Step.rw 1 25 1 true, Step.mv 29 22,
     Step.mv 30 24, Step.mv 43 28, Step.mv 43 29, Step.mv 43 30, Step.mv 43 31, Step.mv 43 32, Step.mv 43 33, Step.mv 43 34,
     Step.rw 15 18 1 true, Step.mv 16 13, Step.rw 3 14 0 true, Step.mv 19 16, Step.rw 8 15 0 false,
     Step.rw 0 33 0 true, Step.mv 40 23, Step.mv 40 24, Step.mv 40 25, Step.mv 40 26, Step.mv 40 27, Step.mv 40 28,
     Step.mv 40 29, Step.rw 12 20 1 true, Step.mv 37 24, Step.rw 9 20 1 true, Step.rw 0 37 0 true, Step.mv 44 26,
     Step.rw 10 22 1 true, Step.rw 1 16 1 true, Step.mv 22 19, Step.mv 23 21, Step.mv 24 23, Step.mv 25 24,
     Step.rw 13 17 0 true, Step.rw 2 21 0 true, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 45 25,
     Step.mv 45 26, Step.mv 45 27, Step.mv 45 28, Step.mv 45 29, Step.mv 45 30, Step.mv 45 31, Step.rw 6 18 0 true,
     Step.mv 25 21, Step.rw 8 20 0 false, Step.rw 4 17 0 false, Step.rw 1 20 2 true, Step.mv 20 17,
     Step.rw 3 18 1 true, Step.rw 8 19 0 true, Step.rw 5 25 0 true, Step.mv 25 20, Step.rw 5 26 0 true,
     Step.mv 26 21, Step.rw 5 27 0 true, Step.mv 27 22, Step.rw 5 19 0 true, Step.mv 19 15, Step.rw 5 20 0 true,
     Step.mv 20 16, Step.rw 5 21 0 true, Step.mv 21 17, Step.rw 5 14 0 true, Step.mv 14 13, Step.rw 5 15 0 true,
     Step.mv 15 14, Step.rw 5 16 0 true, Step.mv 16 15, Step.rw 1 23 2 true, Step.rw 3 10 0 false, Step.mv 10 9,
     Step.rw 1 8 0 false, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.rw 2 7 0 false, Step.rw 1 7 1 false,
     Step.rw 3 6 0 false, Step.rw 3 5 1 false, Step.mv 5 4, Step.rw 1 3 1 false, Step.rw 1 3 2 false,
     Step.rw 3 2 1 false, Step.mv 2 1, Step.rw 3 0 0 false, Step.rw 1 0 2 false, Step.mv 14 12, Step.rw 4 11 1 true,
     Step.mv 15 13, Step.rw 4 12 1 true, Step.rw 2 11 1 true, Step.mv 11 10, Step.rw 4 9 0 true, Step.mv 12 11,
     Step.rw 4 10 0 true, Step.rw 2 13 0 true, Step.rw 1 15 0 true, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.mv 19 13, Step.mv 20 15, Step.rw 14 10 0 true, Step.mv 10 7, Step.mv 11 8, Step.mv 12 9, Step.rw 1 13 1 true,
     Step.rw 1 6 1 true, Step.mv 12 9, Step.mv 13 11, Step.mv 14 13, Step.mv 15 14, Step.rw 13 7 0 true,
     Step.rw 1 19 2 true, Step.rw 2 20 2 true, Step.rw 0 29 0 true, Step.mv 36 23, Step.rw 10 19 2 true, Step.mv 4 2,
     Step.mv 17 6, Step.mv 18 7, Step.mv 19 8, Step.mv 20 9, Step.mv 21 10, Step.rw 16 1 1 true, Step.mv 1 0, Step.mv 4 3,
     Step.mv 5 4, Step.rw 5 2 1 true, Step.mv 2 1, Step.rw 1 7 1 true, Step.mv 2 0, Step.mv 5 4, Step.mv 11 10,
     Step.mv 16 14, Step.mv 17 15, Step.mv 18 16, Step.mv 19 17, Step.mv 22 18, Step.mv 21 19, Step.mv 22 20])
    (by decide +kernel)

/-- Equation 3.93 (supplement: `[ZZ 1 2 D 2 0 1 D 4 1 2]·ω^0 = [D 2 0 1 D 1 1 2 H 1 ZZ 0 1 H 1]·ω^0`). -/
theorem rule_3_93 :
    Holds 3 ([Lt.CZ 0] ++ bD 2 1 ++ bD 4 0)
      (bD 2 1 ++ bD 1 0 ++ [.H 1, .CZ 1, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 8 1, Step.mv 5 4, Step.mv 11 10, Step.rw 1 7 1 false, Step.rw 3 6 1 true, Step.rw 7 8 0 true, Step.mv 10 9,
     Step.rw 2 11 1 true, Step.rw 5 10 1 true, Step.mv 10 9, Step.rw 4 8 0 true, Step.rw 1 13 1 true,
     Step.rw 2 11 0 true, Step.rw 1 9 1 true, Step.rw 1 1 0 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6,
     Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.mv 19 14, Step.mv 20 16, Step.mv 21 18,
     Step.rw 15 11 0 true, Step.mv 13 12, Step.mv 18 17, Step.mv 21 20, Step.rw 5 25 0 true, Step.mv 25 21,
     Step.rw 2 27 0 true, Step.rw 5 26 0 true, Step.mv 26 22, Step.rw 5 27 0 true, Step.mv 27 23,
     Step.rw 5 25 1 true, Step.mv 31 29, Step.mv 32 31, Step.rw 11 27 0 true, Step.rw 5 26 1 true,
     Step.rw 5 27 1 true, Step.rw 1 26 1 true, Step.mv 13 12, Step.mv 14 13, Step.mv 15 14, Step.mv 18 17, Step.mv 24 20,
     Step.mv 25 21, Step.mv 26 22, Step.rw 17 15 0 true, Step.mv 15 12, Step.mv 16 13, Step.mv 19 18,
     Step.rw 0 33 0 true, Step.mv 40 25, Step.rw 8 21 0 true, Step.rw 5 20 0 true, Step.mv 20 19, Step.mv 39 25,
     Step.mv 39 26, Step.mv 39 27, Step.mv 39 28, Step.mv 39 29, Step.mv 39 30, Step.mv 39 31, Step.rw 10 22 0 true,
     Step.rw 5 21 0 true, Step.mv 21 20, Step.rw 1 32 1 true, Step.mv 29 23, Step.mv 30 25, Step.mv 31 27, Step.mv 32 28,
     Step.rw 11 21 0 true, Step.rw 1 21 0 true, Step.mv 14 13, Step.mv 15 14, Step.mv 16 15, Step.mv 23 19,
     Step.mv 24 21, Step.rw 16 16 0 true, Step.mv 16 13, Step.mv 17 14, Step.mv 18 15, Step.rw 1 25 0 true,
     Step.rw 13 18 0 true, Step.rw 5 17 1 true, Step.rw 1 26 0 true, Step.rw 13 19 0 true, Step.rw 5 18 1 true,
     Step.rw 1 27 0 true, Step.rw 13 20 0 true, Step.rw 5 19 1 true, Step.rw 1 19 1 true, Step.rw 0 35 0 true,
     Step.mv 42 20, Step.mv 42 21, Step.rw 9 16 1 true, Step.mv 16 12, Step.mv 17 14, Step.mv 18 16, Step.mv 19 17,
     Step.mv 20 18, Step.rw 0 43 0 true, Step.mv 50 19, Step.mv 50 20, Step.mv 50 21, Step.mv 50 22, Step.mv 50 23,
     Step.mv 50 24, Step.mv 50 25, Step.rw 12 9 0 true, Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.mv 37 17,
     Step.mv 37 18, Step.mv 37 19, Step.mv 37 20, Step.mv 37 21, Step.mv 37 22, Step.mv 37 23, Step.rw 6 10 0 true,
     Step.mv 14 13, Step.rw 7 12 0 false, Step.rw 1 12 2 true, Step.mv 12 10, Step.rw 3 11 1 true,
     Step.rw 7 12 0 true, Step.rw 1 13 2 true, Step.rw 1 1 0 false, Step.rw 3 5 1 false, Step.mv 5 4,
     Step.rw 1 3 1 false, Step.rw 1 3 2 false, Step.rw 3 2 1 false, Step.mv 2 1, Step.rw 3 0 0 false,
     Step.rw 1 0 2 false, Step.rw 3 16 0 false, Step.mv 16 13, Step.rw 1 12 0 false, Step.rw 1 12 0 true,
     Step.rw 14 5 0 true, Step.mv 3 2, Step.mv 8 7, Step.mv 11 10])
    (by decide +kernel)

/-- Equation 3.94 (supplement: `[ZZ 1 2 D 3 0 1 D 1 1 2]·ω^0 = [D 3 0 1 D 4 1 2 H 1 H 0 S 0 H 0 ZZ 1 0 S 0 H 0 S 0 H 1]·ω^7`). -/
theorem rule_3_94 :
    Holds 3 ([Lt.CZ 0] ++ bD 3 1 ++ bD 1 0)
      (bD 3 1 ++ bD 4 0 ++ [.H 1, .H 2, .S 2, .H 2, .CZ 1, .S 2, .H 2, .S 2, .H 1, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM17 db_ok_nil))))))))))))))))))))
    (steps := [Step.mv 2 1, Step.mv 3 2, Step.mv 6 5, Step.mv 11 10, Step.mv 14 13, Step.mv 3 2, Step.rw 5 3 1 false, Step.mv 2 1, Step.mv 6 4,
     Step.rw 19 2 1 false, Step.mv 4 3, Step.mv 5 4, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10, Step.mv 16 11,
     Step.mv 17 12, Step.mv 18 13, Step.mv 19 14, Step.mv 20 15, Step.mv 21 16, Step.mv 22 17, Step.mv 23 18, Step.mv 24 19,
     Step.rw 1 10 1 false, Step.rw 4 9 0 false, Step.mv 11 10, Step.rw 4 8 0 false, Step.mv 10 9,
     Step.rw 12 10 0 false, Step.mv 13 12, Step.mv 15 13, Step.mv 18 14, Step.rw 1 18 1 false, Step.mv 15 12,
     Step.mv 16 13, Step.mv 17 14, Step.rw 17 15 0 false, Step.mv 15 12, Step.mv 19 18, Step.mv 21 19, Step.mv 22 20,
     Step.mv 23 21, Step.rw 1 20 0 false, Step.rw 4 15 0 false, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18,
     Step.rw 4 14 0 false, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17,
     Step.mv 21 18, Step.rw 2 15 1 false, Step.rw 15 7 0 false, Step.rw 1 14 0 false, Step.rw 1 14 1 true,
     Step.mv 15 17, Step.rw 3 15 1 true, Step.mv 16 18, Step.rw 1 16 1 true, Step.mv 17 19, Step.rw 1 14 0 true,
     Step.mv 15 18, Step.rw 3 18 0 true, Step.rw 2 16 2 true, Step.rw 2 16 2 true, Step.rw 1 19 2 true,
     Step.rw 2 20 2 true, Step.rw 2 14 0 true, Step.rw 1 0 2 true, Step.mv 1 2, Step.rw 3 1 1 true,
     Step.rw 1 2 2 true, Step.rw 2 2 1 true, Step.mv 5 6, Step.mv 4 5, Step.mv 3 4, Step.rw 1 3 1 true, Step.mv 4 5,
     Step.rw 3 5 1 true, Step.rw 1 0 0 true, Step.mv 16 15, Step.mv 17 16, Step.rw 1 15 2 false,
     Step.rw 2 28 0 false, Step.rw 11 30 2 false, Step.mv 39 61, Step.mv 38 60, Step.mv 37 59, Step.mv 36 58,
     Step.mv 35 57, Step.mv 34 56, Step.mv 33 55, Step.rw 8 30 2 false, Step.mv 34 55, Step.rw 0 55 0 false,
     Step.rw 1 33 2 false, Step.mv 30 21, Step.mv 31 22, Step.mv 32 23, Step.mv 33 24, Step.rw 2 21 2 false,
     Step.mv 30 21, Step.mv 31 22, Step.mv 32 23, Step.mv 33 24, Step.rw 2 21 2 false, Step.rw 7 15 0 false,
     Step.rw 3 14 1 false, Step.mv 14 13, Step.mv 15 14, Step.mv 16 15, Step.mv 16 9, Step.mv 17 10, Step.rw 1 9 2 false,
     Step.rw 4 12 0 false, Step.rw 4 11 0 false, Step.rw 4 10 0 false, Step.rw 2 11 1 false, Step.rw 7 12 0 true,
     Step.mv 14 13, Step.rw 6 10 0 false, Step.mv 23 47, Step.mv 22 46, Step.mv 21 45, Step.mv 20 44, Step.mv 19 43,
     Step.mv 18 42, Step.mv 17 41, Step.mv 17 14, Step.rw 13 9 0 false, Step.mv 25 53, Step.mv 24 52, Step.mv 23 51,
     Step.mv 22 50, Step.mv 21 49, Step.mv 20 48, Step.mv 19 47, Step.rw 0 53 0 false, Step.mv 13 12, Step.mv 15 13,
     Step.mv 19 14, Step.mv 20 15, Step.rw 10 16 1 false, Step.mv 21 46, Step.mv 20 45, Step.rw 0 45 0 false,
     Step.rw 1 19 1 false, Step.rw 5 19 1 false, Step.rw 14 20 0 false, Step.rw 1 27 0 false,
     Step.rw 5 18 1 false, Step.rw 14 19 0 false, Step.rw 1 26 0 false, Step.rw 5 17 1 false,
     Step.rw 14 18 0 false, Step.rw 1 25 0 false, Step.mv 16 13, Step.mv 17 14, Step.mv 18 15, Step.rw 17 16 0 false,
     Step.mv 16 13, Step.mv 20 19, Step.mv 22 20, Step.mv 23 21, Step.mv 24 22, Step.rw 1 21 0 false,
     Step.rw 12 21 0 false, Step.mv 24 23, Step.mv 26 24, Step.mv 29 25, Step.mv 30 26, Step.mv 31 27, Step.mv 32 28,
     Step.rw 1 32 1 false, Step.mv 21 20, Step.rw 5 21 0 false, Step.rw 11 22 0 false, Step.mv 31 49, Step.mv 30 48,
     Step.mv 29 47, Step.mv 28 46, Step.mv 27 45, Step.mv 26 44, Step.mv 25 43, Step.mv 20 19, Step.rw 5 20 0 false,
     Step.rw 9 21 0 false, Step.mv 25 43, Step.rw 0 43 0 false, Step.mv 14 12, Step.mv 15 13, Step.mv 16 14,
     Step.mv 19 18, Step.rw 18 15 0 false, Step.mv 15 12, Step.mv 18 17, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22,
     Step.mv 26 23, Step.rw 1 26 1 false, Step.rw 5 27 1 false, Step.rw 5 26 1 false, Step.rw 12 27 0 false,
     Step.mv 30 29, Step.mv 32 30, Step.rw 5 25 1 false, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26,
     Step.rw 5 27 0 false, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.rw 5 26 0 false,
     Step.rw 2 27 0 false, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.rw 5 25 0 false,
     Step.mv 13 12, Step.mv 18 17, Step.mv 21 20, Step.rw 16 11 0 false, Step.mv 12 2, Step.mv 15 14, Step.mv 17 15,
     Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.rw 1 0 0 false, Step.rw 1 9 1 false, Step.rw 2 11 0 false,
     Step.rw 1 13 1 false, Step.rw 4 8 0 false, Step.mv 10 9, Step.rw 5 10 1 false, Step.rw 2 11 1 false,
     Step.mv 10 9, Step.rw 7 8 0 false, Step.rw 3 6 1 false, Step.mv 17 16, Step.rw 4 15 1 true, Step.mv 18 17,
     Step.rw 4 16 1 true, Step.rw 2 14 1 true, Step.mv 14 11, Step.rw 4 10 0 true, Step.mv 15 12,
     Step.rw 4 11 0 true, Step.rw 1 16 0 true, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 18 14, Step.mv 19 16,
     Step.rw 17 11 0 true, Step.mv 11 8, Step.mv 12 9, Step.mv 13 10, Step.rw 1 14 1 true, Step.rw 1 7 1 true,
     Step.mv 13 10, Step.mv 14 12, Step.mv 15 14, Step.mv 16 15, Step.rw 12 8 0 true, Step.rw 1 19 2 true,
     Step.rw 2 20 2 true, Step.rw 0 30 0 true, Step.mv 37 23, Step.rw 9 19 2 true, Step.mv 5 3, Step.mv 17 7,
     Step.mv 18 8, Step.mv 19 9, Step.mv 20 10, Step.mv 21 11, Step.rw 19 2 1 true, Step.mv 2 1, Step.mv 5 4, Step.mv 6 5,
     Step.rw 5 3 1 true, Step.mv 3 2, Step.rw 1 8 1 true, Step.mv 3 0, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 6 4,
     Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 12 11, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22])
    (by decide +kernel)

/-- Equation 3.95 (supplement: `[ZZ 1 2 D 3 0 1 D 2 1 2]·ω^0 = [D 2 0 1 D 3 1 2 H 1 S 1 H 1 ZZ 0 1 H 0 S 0 S 1 S 2 S 2]·ω^7`). -/
theorem rule_3_95 :
    Holds 3 ([Lt.CZ 0] ++ bD 3 1 ++ bD 2 0)
      (bD 2 1 ++ bD 3 0 ++ [.H 1, .S 1, .H 1, .CZ 1, .H 2, .S 2, .S 1, .S 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 2 1, Step.mv 3 2, Step.mv 6 5, Step.mv 12 11, Step.rw 1 8 1 false, Step.mv 3 2, Step.rw 5 3 1 false, Step.mv 2 1,
     Step.mv 6 4, Step.rw 16 2 1 false, Step.mv 4 3, Step.mv 5 4, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10,
     Step.mv 16 11, Step.mv 17 12, Step.mv 18 13, Step.mv 19 14, Step.mv 20 15, Step.rw 13 8 0 false, Step.mv 11 10,
     Step.mv 13 11, Step.mv 16 12, Step.rw 1 7 1 false, Step.rw 1 14 1 false, Step.mv 11 8, Step.mv 12 9, Step.mv 13 10,
     Step.rw 14 11 0 false, Step.mv 11 8, Step.mv 15 14, Step.mv 17 15, Step.mv 18 16, Step.mv 19 17,
     Step.rw 1 16 0 false, Step.rw 4 11 0 false, Step.mv 13 12, Step.mv 14 13, Step.mv 15 14, Step.rw 4 10 0 false,
     Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13, Step.mv 17 14,
     Step.rw 2 11 1 false, Step.rw 1 0 2 true, Step.mv 1 2, Step.rw 3 1 1 true, Step.rw 1 2 2 true,
     Step.rw 1 2 1 true, Step.mv 3 4, Step.rw 3 4 1 true, Step.rw 3 5 0 true, Step.rw 1 6 1 true, Step.rw 2 6 0 true,
     Step.mv 9 10, Step.mv 8 9, Step.mv 7 8, Step.rw 1 7 0 true, Step.mv 8 9, Step.rw 3 9 0 true, Step.rw 3 10 1 true,
     Step.mv 24 23, Step.mv 25 24, Step.rw 1 23 2 false, Step.mv 17 16, Step.rw 5 17 0 false, Step.mv 16 15,
     Step.rw 5 16 0 false, Step.mv 15 14, Step.rw 5 15 0 false, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20,
     Step.mv 22 21, Step.rw 5 22 0 false, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20,
     Step.rw 5 21 0 false, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.rw 5 20 0 false,
     Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.rw 5 28 0 false, Step.mv 23 22,
     Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.rw 5 27 0 false, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.rw 5 26 0 false, Step.rw 8 20 0 false, Step.rw 3 19 1 false,
     Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 21 17, Step.mv 22 18, Step.rw 1 17 2 false,
     Step.rw 4 18 0 true, Step.rw 8 21 0 true, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25,
     Step.rw 6 19 0 false, Step.mv 32 47, Step.mv 31 46, Step.mv 30 45, Step.mv 29 44, Step.mv 28 43, Step.mv 27 42,
     Step.mv 26 41, Step.mv 26 23, Step.mv 27 24, Step.mv 28 25, Step.mv 29 26, Step.rw 2 22 0 false,
     Step.rw 13 18 0 false, Step.mv 21 20, Step.mv 23 21, Step.mv 26 22, Step.rw 1 17 1 false, Step.rw 10 23 1 false,
     Step.mv 27 39, Step.rw 0 39 0 false, Step.rw 9 21 1 false, Step.mv 25 39, Step.rw 12 21 1 false, Step.mv 30 41,
     Step.mv 29 40, Step.mv 28 39, Step.mv 27 38, Step.mv 26 37, Step.mv 25 36, Step.mv 24 35, Step.rw 0 35 0 false,
     Step.rw 8 16 0 true, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.rw 3 15 0 false, Step.mv 15 14,
     Step.mv 16 15, Step.mv 17 16, Step.rw 15 19 1 false, Step.mv 35 45, Step.mv 34 44, Step.mv 33 43, Step.mv 32 42,
     Step.mv 31 41, Step.mv 30 40, Step.mv 29 39, Step.mv 24 23, Step.mv 26 24, Step.mv 27 25, Step.mv 28 26, Step.mv 29 27,
     Step.mv 30 28, Step.mv 31 29, Step.mv 32 30, Step.mv 33 31, Step.rw 1 26 1 false, Step.mv 30 22, Step.mv 31 23,
     Step.mv 32 24, Step.mv 33 25, Step.rw 2 22 2 false, Step.rw 5 18 1 true, Step.rw 7 19 1 false, Step.mv 32 43,
     Step.mv 31 42, Step.mv 30 41, Step.mv 29 40, Step.mv 28 39, Step.mv 27 38, Step.mv 26 37, Step.rw 0 43 0 false,
     Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29,
     Step.mv 31 30, Step.mv 32 31, Step.mv 33 32, Step.rw 11 22 1 false, Step.mv 27 36, Step.mv 26 35,
     Step.rw 0 35 0 false, Step.rw 14 18 1 false, Step.mv 22 21, Step.mv 24 22, Step.mv 25 23, Step.mv 26 24,
     Step.mv 27 25, Step.mv 28 26, Step.mv 29 27, Step.mv 30 28, Step.mv 31 29, Step.mv 32 30, Step.mv 33 31, Step.mv 34 32,
     Step.mv 17 13, Step.mv 18 14, Step.rw 1 13 1 false, Step.rw 1 21 1 false, Step.rw 2 19 1 false,
     Step.rw 1 18 1 false, Step.mv 23 18, Step.mv 24 19, Step.mv 25 20, Step.mv 26 21, Step.rw 2 18 2 false,
     Step.mv 17 14, Step.mv 18 15, Step.rw 14 16 0 false, Step.mv 16 14, Step.mv 20 19, Step.mv 22 20, Step.mv 23 21,
     Step.mv 24 22, Step.mv 25 23, Step.mv 26 24, Step.rw 1 13 0 false, Step.rw 1 19 0 false, Step.rw 2 17 0 false,
     Step.rw 8 12 0 false, Step.rw 3 10 1 false, Step.rw 4 12 0 false, Step.mv 14 13, Step.rw 3 11 0 false,
     Step.mv 11 10, Step.rw 5 11 1 true, Step.rw 5 12 1 true, Step.rw 1 13 1 true, Step.rw 2 14 1 true,
     Step.rw 0 23 0 true, Step.mv 30 17, Step.rw 10 13 1 true, Step.rw 2 11 0 true, Step.rw 1 13 0 true, Step.mv 8 6,
     Step.mv 17 10, Step.mv 18 11, Step.mv 19 12, Step.mv 20 13, Step.mv 21 14, Step.rw 16 5 0 true, Step.mv 5 0,
     Step.mv 8 7, Step.mv 9 8, Step.rw 5 6 0 true, Step.mv 6 1, Step.rw 1 7 1 true, Step.mv 2 0, Step.mv 3 1, Step.mv 5 2,
     Step.mv 5 3, Step.mv 6 4, Step.mv 7 5, Step.mv 8 6, Step.mv 11 10, Step.mv 16 14, Step.mv 17 15, Step.mv 18 16,
     Step.mv 19 17, Step.mv 21 18, Step.mv 22 19, Step.mv 22 20])
    (by decide +kernel)

/-- Equation 3.96 (supplement: `[ZZ 1 2 D 3 0 1 D 3 1 2]·ω^0 = [D 2 0 1 D 2 1 2 ZZ 0 1 H 0 S 0 H 1 S 1]·ω^0`). -/
theorem rule_3_96 :
    Holds 3 ([Lt.CZ 0] ++ bD 3 1 ++ bD 3 0)
      (bD 2 1 ++ bD 2 0 ++ [.CZ 1, .H 2, .S 2, .H 1, .S 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil))))))))))))))))
    (steps := [Step.mv 10 1, Step.mv 11 2, Step.mv 4 3, Step.mv 5 4, Step.mv 8 7, Step.mv 14 13, Step.rw 1 10 1 false, Step.mv 5 4,
     Step.rw 5 5 1 false, Step.mv 4 3, Step.mv 8 6, Step.rw 15 4 1 false, Step.mv 6 5, Step.mv 7 6, Step.mv 14 9,
     Step.mv 15 10, Step.mv 16 11, Step.mv 17 12, Step.mv 18 13, Step.mv 19 14, Step.mv 20 15, Step.mv 21 16, Step.mv 22 17,
     Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10,
     Step.mv 12 11, Step.rw 5 12 0 false, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6,
     Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 15 13, Step.rw 15 11 0 false, Step.mv 13 12,
     Step.mv 14 13, Step.mv 21 16, Step.mv 22 17, Step.mv 23 18, Step.mv 24 19, Step.mv 25 20, Step.rw 1 19 0 false,
     Step.rw 12 8 0 false, Step.mv 11 10, Step.mv 13 11, Step.mv 16 12, Step.mv 17 13, Step.rw 1 7 1 false,
     Step.rw 1 15 1 false, Step.mv 12 9, Step.mv 13 10, Step.mv 14 11, Step.rw 13 12 0 false, Step.mv 12 9,
     Step.mv 16 15, Step.mv 18 16, Step.mv 19 17, Step.mv 20 18, Step.mv 21 19, Step.mv 22 20, Step.rw 1 17 0 false,
     Step.rw 2 15 0 false, Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.rw 2 14 1 false,
     Step.rw 4 12 0 false, Step.mv 14 13, Step.rw 4 11 0 false, Step.mv 13 12, Step.rw 3 11 1 true,
     Step.rw 8 12 0 true, Step.mv 14 13, Step.mv 20 15, Step.rw 4 14 1 true, Step.mv 21 16, Step.rw 4 15 1 true,
     Step.mv 22 17, Step.rw 4 16 1 true, Step.rw 5 17 1 true, Step.mv 17 14, Step.rw 5 18 1 true, Step.mv 18 15,
     Step.rw 5 19 1 true, Step.mv 19 16, Step.mv 14 13, Step.rw 4 12 0 true, Step.mv 15 14, Step.rw 4 13 0 true,
     Step.mv 16 15, Step.rw 4 14 0 true, Step.rw 1 15 1 true, Step.rw 0 27 0 true, Step.mv 34 16,
     Step.rw 9 12 1 true, Step.mv 33 15, Step.mv 33 16, Step.mv 33 17, Step.mv 33 18, Step.mv 33 19, Step.mv 33 20,
     Step.mv 33 21, Step.rw 11 12 1 true, Step.rw 0 31 0 true, Step.mv 38 16, Step.rw 9 12 1 true, Step.mv 37 18,
     Step.rw 10 14 1 true, Step.mv 23 13, Step.mv 24 15, Step.rw 13 10 1 true, Step.mv 21 14, Step.rw 0 33 0 true,
     Step.mv 40 18, Step.mv 40 19, Step.mv 40 20, Step.mv 40 21, Step.mv 40 22, Step.mv 40 23, Step.mv 40 24,
     Step.rw 7 11 1 true, Step.rw 5 10 1 false, Step.rw 2 18 2 true, Step.rw 2 16 1 true, Step.rw 1 18 1 true,
     Step.mv 24 15, Step.mv 25 17, Step.mv 39 21, Step.mv 39 22, Step.mv 39 23, Step.mv 39 24, Step.mv 39 25, Step.mv 39 26,
     Step.mv 39 27, Step.rw 14 11 1 true, Step.rw 3 7 0 true, Step.mv 12 10, Step.rw 8 9 0 false,
     Step.rw 0 29 0 true, Step.mv 36 16, Step.mv 36 17, Step.mv 36 18, Step.mv 36 19, Step.mv 36 20, Step.mv 36 21,
     Step.mv 36 22, Step.rw 11 13 1 true, Step.mv 33 17, Step.rw 9 13 1 true, Step.rw 0 33 0 true, Step.mv 40 19,
     Step.rw 10 15 1 true, Step.rw 2 11 0 true, Step.rw 1 10 1 true, Step.mv 19 13, Step.mv 20 15, Step.mv 21 17,
     Step.mv 22 18, Step.rw 12 11 0 true, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 41 19, Step.mv 41 20,
     Step.mv 41 21, Step.mv 41 22, Step.mv 41 23, Step.mv 41 24, Step.mv 41 25, Step.rw 6 12 0 true, Step.mv 18 15,
     Step.rw 8 14 0 false, Step.rw 4 11 0 false, Step.rw 1 22 1 true, Step.rw 1 15 1 true, Step.mv 21 18,
     Step.mv 22 20, Step.mv 23 22, Step.mv 24 23, Step.rw 12 16 0 true, Step.mv 24 16, Step.mv 25 18,
     Step.rw 13 13 1 true, Step.rw 1 16 2 true, Step.mv 16 11, Step.rw 3 12 1 true, Step.rw 8 13 0 true,
     Step.rw 5 14 1 true, Step.rw 5 15 1 true, Step.rw 5 16 1 true, Step.rw 4 13 0 true, Step.rw 4 14 0 true,
     Step.rw 4 15 0 true, Step.rw 5 12 1 true, Step.mv 12 11, Step.rw 5 13 1 true, Step.mv 13 12,
     Step.rw 5 14 1 true, Step.mv 14 13, Step.rw 1 17 2 true, Step.rw 3 7 0 false, Step.rw 3 6 1 false, Step.mv 6 5,
     Step.rw 1 4 1 false, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.rw 2 3 1 false, Step.rw 1 3 2 false,
     Step.rw 3 2 1 false, Step.mv 2 1, Step.rw 3 0 0 false, Step.rw 1 0 2 false, Step.rw 1 5 1 true, Step.mv 3 2,
     Step.mv 9 8, Step.mv 15 13, Step.mv 16 14])
    (by decide +kernel)

/-- Equation 3.97 (supplement: `[ZZ 1 2 D 3 0 1 D 4 1 2]·ω^0 = [D 3 0 1 D 1 1 2 H 1 H 0 S 0 H 0 ZZ 1 0 S 0 H 0 S 0 H 1]·ω^7`). -/
theorem rule_3_97 :
    Holds 3 ([Lt.CZ 0] ++ bD 3 1 ++ bD 4 0)
      (bD 3 1 ++ bD 1 0 ++ [.H 1, .H 2, .S 2, .H 2, .CZ 1, .S 2, .H 2, .S 2, .H 1, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM17 db_ok_nil))))))))))))))))))))
    (steps := [Step.mv 10 1, Step.mv 3 2, Step.mv 4 3, Step.mv 7 6, Step.mv 13 12, Step.rw 1 9 1 false, Step.mv 4 3, Step.rw 5 4 1 false,
     Step.mv 3 2, Step.mv 7 5, Step.rw 19 3 1 false, Step.mv 5 4, Step.mv 6 5, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10,
     Step.mv 16 11, Step.mv 17 12, Step.mv 18 13, Step.mv 19 14, Step.mv 20 15, Step.mv 21 16, Step.rw 12 9 0 false,
     Step.mv 12 11, Step.mv 14 12, Step.mv 17 13, Step.rw 1 8 1 false, Step.rw 1 15 1 false, Step.rw 4 14 0 false,
     Step.mv 16 15, Step.rw 4 13 0 false, Step.mv 15 14, Step.mv 12 9, Step.rw 17 10 0 false, Step.mv 10 9,
     Step.mv 14 13, Step.mv 16 14, Step.mv 17 15, Step.mv 18 16, Step.rw 1 15 0 false, Step.mv 15 12, Step.mv 16 13,
     Step.mv 17 14, Step.mv 18 15, Step.rw 2 12 1 false, Step.rw 3 7 1 true, Step.rw 7 9 0 true, Step.mv 11 10,
     Step.rw 2 12 1 true, Step.rw 5 11 1 true, Step.mv 11 10, Step.rw 4 9 0 true, Step.rw 1 14 1 true,
     Step.rw 2 12 0 true, Step.rw 1 10 1 true, Step.rw 1 1 0 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6,
     Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 20 15, Step.mv 21 17,
     Step.mv 22 19, Step.rw 16 12 0 true, Step.mv 14 13, Step.mv 19 18, Step.mv 22 21, Step.rw 5 26 0 true,
     Step.mv 26 22, Step.rw 2 28 0 true, Step.rw 5 27 0 true, Step.mv 27 23, Step.rw 5 28 0 true, Step.mv 28 24,
     Step.rw 5 26 1 true, Step.mv 32 30, Step.mv 33 32, Step.rw 12 28 0 true, Step.rw 5 27 1 true,
     Step.rw 5 28 1 true, Step.rw 1 27 1 true, Step.mv 14 13, Step.mv 15 14, Step.mv 16 15, Step.mv 19 18, Step.mv 25 21,
     Step.mv 26 22, Step.mv 27 23, Step.rw 18 16 0 true, Step.mv 16 13, Step.mv 17 14, Step.mv 20 19,
     Step.rw 0 41 0 true, Step.mv 48 26, Step.rw 9 22 0 true, Step.rw 5 21 0 true, Step.mv 21 20, Step.mv 47 26,
     Step.mv 47 27, Step.mv 47 28, Step.mv 47 29, Step.mv 47 30, Step.mv 47 31, Step.mv 47 32, Step.rw 11 23 0 true,
     Step.rw 5 22 0 true, Step.mv 22 21, Step.rw 1 33 1 true, Step.mv 30 24, Step.mv 31 26, Step.mv 32 28, Step.mv 33 29,
     Step.rw 12 22 0 true, Step.rw 1 22 0 true, Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.mv 24 20,
     Step.mv 25 22, Step.rw 17 17 0 true, Step.mv 17 14, Step.mv 18 15, Step.mv 19 16, Step.rw 1 26 0 true,
     Step.rw 14 19 0 true, Step.rw 5 18 1 true, Step.rw 1 27 0 true, Step.rw 14 20 0 true, Step.rw 5 19 1 true,
     Step.rw 1 28 0 true, Step.rw 14 21 0 true, Step.rw 5 20 1 true, Step.rw 1 20 1 true, Step.rw 0 43 0 true,
     Step.mv 50 21, Step.mv 50 22, Step.rw 10 17 1 true, Step.mv 17 13, Step.mv 18 15, Step.mv 19 17, Step.mv 20 18,
     Step.mv 21 19, Step.rw 0 51 0 true, Step.mv 58 20, Step.mv 58 21, Step.mv 58 22, Step.mv 58 23, Step.mv 58 24,
     Step.mv 58 25, Step.mv 58 26, Step.rw 13 10 0 true, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 45 18,
     Step.mv 45 19, Step.mv 45 20, Step.mv 45 21, Step.mv 45 22, Step.mv 45 23, Step.mv 45 24, Step.rw 6 11 0 true,
     Step.mv 15 14, Step.rw 7 13 0 false, Step.rw 2 12 1 true, Step.rw 4 11 0 true, Step.rw 4 12 0 true,
     Step.rw 4 13 0 true, Step.rw 1 17 2 true, Step.mv 17 14, Step.rw 3 15 1 true, Step.rw 7 16 0 true,
     Step.rw 2 38 2 true, Step.rw 1 41 2 true, Step.rw 0 49 0 true, Step.mv 56 42, Step.rw 8 38 2 true,
     Step.mv 55 41, Step.mv 55 42, Step.mv 55 43, Step.mv 55 44, Step.mv 55 45, Step.mv 55 46, Step.mv 55 47,
     Step.rw 11 38 2 true, Step.rw 2 29 0 true, Step.rw 1 17 2 true, Step.rw 1 1 0 false, Step.rw 3 6 1 false,
     Step.mv 6 5, Step.rw 1 4 1 false, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.rw 2 3 1 false, Step.rw 1 3 2 false,
     Step.rw 3 2 1 false, Step.mv 2 1, Step.rw 3 0 0 false, Step.rw 1 0 2 false, Step.rw 2 13 0 false,
     Step.rw 3 17 0 false, Step.mv 17 14, Step.rw 1 13 0 false, Step.rw 2 22 2 false, Step.rw 1 21 2 false,
     Step.rw 2 18 2 false, Step.mv 16 13, Step.mv 17 14, Step.mv 18 17, Step.rw 4 16 1 true, Step.mv 19 18,
     Step.rw 4 17 1 true, Step.rw 1 13 0 true, Step.rw 15 6 0 true, Step.rw 2 17 1 true, Step.mv 17 14,
     Step.rw 4 13 0 true, Step.mv 18 15, Step.rw 4 14 0 true, Step.rw 1 19 0 true, Step.mv 12 11, Step.mv 13 12,
     Step.mv 14 13, Step.mv 21 17, Step.mv 22 19, Step.rw 17 14 0 true, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13,
     Step.rw 1 17 1 true, Step.mv 14 11, Step.mv 15 13, Step.mv 16 15, Step.mv 17 16, Step.rw 12 9 0 true, Step.mv 9 8,
     Step.rw 4 7 0 true, Step.mv 10 9, Step.rw 4 8 0 true, Step.rw 1 20 2 true, Step.rw 2 21 2 true,
     Step.rw 0 31 0 true, Step.mv 38 24, Step.rw 9 20 2 true, Step.rw 1 9 1 true, Step.mv 4 2, Step.mv 20 6,
     Step.mv 21 7, Step.mv 22 8, Step.mv 23 9, Step.mv 24 10, Step.rw 19 1 1 true, Step.mv 1 0, Step.mv 4 3, Step.mv 5 4,
     Step.rw 5 2 1 true, Step.mv 2 1, Step.mv 2 0, Step.mv 5 4, Step.mv 10 9, Step.mv 13 12, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23])
    (by decide +kernel)

/-- Equation 3.98 (supplement: `[ZZ 1 2 D 4 0 1 D 1 1 2]·ω^0 = [D 4 0 1 D 1 1 2 H 0 H 1 ZZ 0 1 H 0 H 1]·ω^0`). -/
theorem rule_3_98 :
    Holds 3 ([Lt.CZ 0] ++ bD 4 1 ++ bD 1 0)
      (bD 4 1 ++ bD 1 0 ++ [.H 2, .H 1, .CZ 1, .H 2, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hL18 (db_ok_cons hL20 (db_ok_cons hM16 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 2 1, Step.mv 5 4, Step.mv 10 9, Step.mv 13 12, Step.rw 15 7 0 false, Step.rw 1 14 0 false, Step.rw 1 1 0 true,
     Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.rw 3 8 0 true, Step.rw 1 9 1 true,
     Step.rw 1 9 0 true, Step.mv 11 10, Step.rw 3 11 0 true, Step.rw 1 24 2 true, Step.rw 1 12 1 true,
     Step.rw 1 2 1 true, Step.mv 2 1, Step.mv 3 2, Step.mv 5 3, Step.mv 5 4, Step.mv 8 7, Step.mv 28 10, Step.mv 13 12,
     Step.rw 16 4 0 true, Step.mv 4 3, Step.mv 6 4, Step.mv 6 5, Step.mv 9 8, Step.mv 12 11, Step.mv 14 12, Step.mv 14 13,
     Step.mv 15 14, Step.mv 16 15, Step.rw 2 16 1 true, Step.rw 1 17 1 true, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6,
     Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 13 12, Step.rw 17 10 0 true, Step.mv 10 4, Step.mv 11 5, Step.mv 14 13,
     Step.rw 1 19 1 true, Step.rw 2 16 0 true, Step.mv 20 16, Step.mv 21 18, Step.mv 22 20, Step.mv 23 21,
     Step.rw 12 14 0 true, Step.rw 4 17 0 true, Step.mv 17 14, Step.rw 4 18 0 true, Step.mv 18 15,
     Step.rw 2 20 0 true, Step.rw 4 19 0 true, Step.mv 19 16, Step.rw 0 42 0 true, Step.mv 49 17,
     Step.rw 9 13 0 true, Step.mv 6 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 17 13,
     Step.mv 48 17, Step.mv 48 18, Step.mv 48 19, Step.mv 48 20, Step.mv 48 21, Step.mv 48 22, Step.mv 48 23,
     Step.rw 6 10 0 true, Step.rw 2 21 1 true, Step.rw 1 23 1 true, Step.rw 1 20 0 true, Step.rw 0 46 0 true,
     Step.mv 53 21, Step.rw 8 17 0 true, Step.mv 52 20, Step.mv 52 21, Step.mv 52 22, Step.mv 52 23, Step.mv 52 24,
     Step.mv 52 25, Step.mv 52 26, Step.rw 11 17 0 true, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25,
     Step.rw 14 12 0 true, Step.rw 1 25 1 true, Step.rw 0 44 0 true, Step.mv 51 26, Step.mv 51 27,
     Step.rw 10 22 1 true, Step.mv 22 18, Step.mv 23 20, Step.mv 24 22, Step.mv 25 23, Step.mv 26 24,
     Step.rw 0 52 0 true, Step.mv 59 25, Step.mv 59 26, Step.mv 59 27, Step.mv 59 28, Step.mv 59 29, Step.mv 59 30,
     Step.mv 59 31, Step.rw 13 15 0 true, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 46 23, Step.mv 46 24,
     Step.mv 46 25, Step.mv 46 26, Step.mv 46 27, Step.mv 46 28, Step.mv 46 29, Step.rw 5 16 0 true, Step.mv 20 18,
     Step.mv 21 20, Step.rw 7 19 0 false, Step.rw 15 20 0 true, Step.rw 1 5 2 true, Step.rw 1 1 1 false,
     Step.rw 3 0 0 false, Step.rw 1 1 2 false, Step.rw 3 23 0 false, Step.mv 23 22, Step.rw 1 21 0 false,
     Step.rw 1 21 1 false, Step.rw 3 20 0 false, Step.mv 20 19, Step.rw 1 18 0 false, Step.rw 1 18 1 false,
     Step.rw 3 17 0 false, Step.rw 1 13 0 true, Step.rw 15 6 0 true, Step.mv 1 0, Step.mv 4 3, Step.mv 9 8,
     Step.mv 12 11, Step.mv 16 15, Step.mv 19 18])
    (by decide +kernel)

/-- Equation 3.99 (supplement: `[ZZ 1 2 D 4 0 1 D 2 1 2]·ω^0 = [D 1 0 1 D 2 1 2 H 0 ZZ 0 1 H 0]·ω^0`). -/
theorem rule_3_99 :
    Holds 3 ([Lt.CZ 0] ++ bD 4 1 ++ bD 2 0)
      (bD 1 1 ++ bD 2 0 ++ [.H 2, .CZ 1, .H 2]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 2 1, Step.mv 5 4, Step.mv 11 10, Step.rw 1 7 1 false, Step.rw 2 9 1 true, Step.mv 9 8, Step.rw 4 7 0 true,
     Step.rw 5 6 1 true, Step.mv 6 5, Step.rw 1 16 2 true, Step.rw 2 17 2 true, Step.rw 1 11 1 true,
     Step.rw 1 6 1 true, Step.mv 20 11, Step.mv 13 12, Step.mv 21 13, Step.mv 15 14, Step.mv 22 15, Step.mv 23 16,
     Step.rw 16 7 0 true, Step.mv 10 9, Step.mv 11 10, Step.mv 18 17, Step.mv 22 18, Step.mv 20 19, Step.mv 21 20,
     Step.mv 29 23, Step.rw 4 22 1 true, Step.rw 2 30 2 true, Step.mv 30 24, Step.rw 4 23 1 true, Step.mv 31 25,
     Step.rw 4 24 1 true, Step.rw 1 29 1 true, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 34 27,
     Step.mv 35 29, Step.rw 13 24 1 true, Step.mv 24 20, Step.mv 25 21, Step.mv 26 22, Step.rw 1 18 0 true,
     Step.mv 21 19, Step.mv 22 20, Step.mv 23 21, Step.mv 24 22, Step.rw 3 23 0 true, Step.mv 27 24, Step.mv 28 25,
     Step.mv 29 26, Step.mv 30 27, Step.mv 31 29, Step.rw 7 28 0 false, Step.mv 19 18, Step.rw 4 17 0 true,
     Step.mv 20 19, Step.rw 4 18 0 true, Step.mv 21 20, Step.rw 4 19 0 true, Step.rw 1 18 1 true,
     Step.rw 11 11 1 true, Step.rw 1 26 2 true, Step.mv 11 10, Step.mv 12 11, Step.mv 15 14, Step.mv 24 17,
     Step.mv 25 18, Step.mv 26 19, Step.rw 15 12 1 true, Step.mv 12 10, Step.mv 13 11, Step.mv 16 15,
     Step.rw 1 28 2 true, Step.rw 2 18 1 true, Step.mv 29 18, Step.mv 30 20, Step.mv 31 22, Step.mv 32 23,
     Step.rw 10 16 1 true, Step.rw 2 29 2 true, Step.mv 29 20, Step.rw 4 19 1 true, Step.mv 30 21,
     Step.rw 4 20 1 true, Step.rw 1 22 1 true, Step.rw 0 45 0 true, Step.mv 52 29, Step.mv 52 30, Step.mv 52 31,
     Step.mv 52 32, Step.rw 9 23 1 true, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19,
     Step.mv 33 23, Step.mv 34 25, Step.rw 13 20 1 true, Step.mv 20 15, Step.mv 21 16, Step.mv 22 17,
     Step.rw 5 23 1 true, Step.mv 23 18, Step.rw 5 24 1 true, Step.mv 24 19, Step.rw 1 20 2 true, Step.mv 46 27,
     Step.mv 46 28, Step.mv 46 29, Step.mv 46 30, Step.rw 9 21 2 true, Step.mv 20 15, Step.mv 21 17, Step.mv 22 19,
     Step.mv 23 20, Step.rw 10 13 1 true, Step.rw 1 20 1 true, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13,
     Step.mv 15 14, Step.mv 22 18, Step.mv 23 20, Step.rw 13 15 1 true, Step.mv 15 11, Step.mv 16 12, Step.mv 17 13,
     Step.rw 4 9 0 true, Step.rw 4 10 0 true, Step.rw 4 11 0 true, Step.rw 1 11 1 true, Step.rw 0 39 0 true,
     Step.mv 46 12, Step.mv 46 13, Step.rw 8 8 1 true, Step.mv 18 9, Step.mv 19 11, Step.rw 0 47 0 true, Step.mv 54 15,
     Step.mv 54 16, Step.mv 54 17, Step.mv 54 18, Step.mv 54 19, Step.mv 54 20, Step.mv 54 21, Step.rw 14 5 1 true,
     Step.mv 14 9, Step.mv 41 13, Step.mv 41 14, Step.mv 41 15, Step.mv 41 16, Step.mv 41 17, Step.mv 41 18, Step.mv 41 19,
     Step.rw 6 6 1 true, Step.rw 7 8 0 true, Step.rw 12 9 1 true, Step.rw 1 21 0 true, Step.rw 1 4 1 false,
     Step.rw 3 3 1 false, Step.mv 3 2, Step.rw 1 1 1 false, Step.mv 2 1, Step.rw 3 0 0 false, Step.rw 1 0 2 false,
     Step.rw 1 11 0 false, Step.rw 1 14 0 false, Step.rw 1 14 1 false, Step.rw 3 13 0 false, Step.mv 13 11,
     Step.rw 1 7 1 true, Step.mv 2 1, Step.mv 5 4, Step.mv 11 10])
    (by decide +kernel)

/-- Equation 3.100 (supplement: `[ZZ 1 2 D 4 0 1 D 3 1 2]·ω^0 = [D 1 0 1 D 3 1 2 H 0 H 1 S 1 H 1 ZZ 0 1 H 0 S 1 H 1 S 1]·ω^7`). -/
theorem rule_3_100 :
    Holds 3 ([Lt.CZ 0] ++ bD 4 1 ++ bD 3 0)
      (bD 1 1 ++ bD 3 0 ++ [.H 2, .H 1, .S 1, .H 1, .CZ 1, .H 2, .S 1, .H 1, .S 1, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL18 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM17 (db_ok_cons hM21 db_ok_nil)))))))))))))))))))))
    (steps := [Step.mv 9 1, Step.mv 10 2, Step.mv 4 3, Step.mv 7 6, Step.mv 13 12, Step.rw 1 9 1 false, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4,
     Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.rw 5 8 0 false, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5,
     Step.mv 7 6, Step.mv 11 9, Step.rw 19 7 0 false, Step.mv 9 8, Step.mv 10 9, Step.mv 17 12, Step.mv 18 13, Step.mv 19 14,
     Step.mv 20 15, Step.mv 21 16, Step.rw 1 15 0 false, Step.rw 2 10 1 true, Step.mv 10 8, Step.rw 4 7 0 true,
     Step.rw 5 6 1 true, Step.mv 6 5, Step.rw 1 24 2 true, Step.rw 2 25 2 true, Step.rw 1 12 1 true,
     Step.rw 1 6 1 true, Step.mv 28 11, Step.mv 14 12, Step.mv 29 13, Step.mv 16 14, Step.mv 30 15, Step.mv 31 16,
     Step.rw 20 7 0 true, Step.mv 10 9, Step.mv 11 10, Step.mv 18 17, Step.mv 22 18, Step.mv 23 19, Step.mv 21 20,
     Step.mv 22 21, Step.mv 37 24, Step.rw 4 23 1 true, Step.rw 2 38 2 true, Step.mv 38 25, Step.rw 4 24 1 true,
     Step.mv 39 26, Step.rw 4 25 1 true, Step.rw 1 30 1 true, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24,
     Step.mv 42 28, Step.mv 43 30, Step.rw 16 25 1 true, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23,
     Step.rw 1 19 0 true, Step.mv 22 20, Step.mv 23 21, Step.mv 24 22, Step.mv 25 23, Step.rw 3 24 0 true, Step.mv 28 25,
     Step.mv 29 26, Step.mv 30 27, Step.mv 31 28, Step.mv 32 30, Step.rw 7 29 0 false, Step.mv 20 18,
     Step.rw 4 17 0 true, Step.mv 21 19, Step.rw 4 18 0 true, Step.mv 22 20, Step.rw 4 19 0 true,
     Step.rw 1 18 1 true, Step.rw 14 11 1 true, Step.rw 1 27 2 true, Step.mv 11 10, Step.mv 12 11, Step.mv 15 14,
     Step.mv 25 17, Step.mv 26 18, Step.mv 27 19, Step.rw 18 12 1 true, Step.mv 12 10, Step.mv 13 11, Step.mv 16 15,
     Step.rw 1 29 2 true, Step.rw 2 18 1 true, Step.mv 30 18, Step.mv 31 20, Step.mv 32 22, Step.mv 33 23,
     Step.rw 13 16 1 true, Step.rw 2 30 2 true, Step.mv 30 20, Step.rw 4 19 1 true, Step.mv 31 21,
     Step.rw 4 20 1 true, Step.rw 1 22 1 true, Step.rw 0 53 0 true, Step.mv 60 29, Step.mv 60 30, Step.mv 60 31,
     Step.mv 60 32, Step.rw 11 23 1 true, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19,
     Step.mv 34 23, Step.mv 35 25, Step.rw 16 20 1 true, Step.mv 20 15, Step.mv 21 16, Step.mv 22 17,
     Step.rw 5 23 1 true, Step.mv 23 18, Step.rw 5 24 1 true, Step.mv 24 19, Step.rw 1 20 2 true, Step.mv 54 27,
     Step.mv 54 28, Step.mv 54 29, Step.mv 54 30, Step.rw 11 21 2 true, Step.mv 20 15, Step.mv 21 17, Step.mv 22 19,
     Step.mv 23 20, Step.rw 13 13 1 true, Step.rw 1 20 1 true, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13,
     Step.mv 15 14, Step.mv 22 18, Step.mv 23 20, Step.rw 16 15 1 true, Step.mv 15 11, Step.mv 16 12, Step.mv 17 13,
     Step.rw 4 9 0 true, Step.rw 4 10 0 true, Step.rw 4 11 0 true, Step.rw 1 11 1 true, Step.rw 0 47 0 true,
     Step.mv 54 12, Step.mv 54 13, Step.rw 10 8 1 true, Step.mv 18 9, Step.mv 19 11, Step.rw 0 55 0 true, Step.mv 62 15,
     Step.mv 62 16, Step.mv 62 17, Step.mv 62 18, Step.mv 62 19, Step.mv 62 20, Step.mv 62 21, Step.rw 17 5 1 true,
     Step.mv 14 9, Step.mv 49 13, Step.mv 49 14, Step.mv 49 15, Step.mv 49 16, Step.mv 49 17, Step.mv 49 18, Step.mv 49 19,
     Step.rw 6 6 1 true, Step.rw 7 8 0 true, Step.rw 15 9 1 true, Step.rw 2 24 1 true, Step.rw 1 27 1 true,
     Step.rw 0 45 0 true, Step.mv 52 28, Step.rw 8 24 1 true, Step.mv 51 27, Step.mv 51 28, Step.mv 51 29, Step.mv 51 30,
     Step.mv 51 31, Step.mv 51 32, Step.mv 51 33, Step.rw 12 24 1 true, Step.rw 1 22 0 true, Step.rw 2 23 0 true,
     Step.rw 1 4 1 false, Step.rw 3 3 1 false, Step.mv 3 2, Step.rw 1 1 1 false, Step.mv 2 1, Step.rw 3 0 0 false,
     Step.rw 1 0 2 false, Step.rw 2 13 0 false, Step.rw 1 12 0 false, Step.rw 2 18 1 false, Step.rw 1 17 1 false,
     Step.rw 2 14 1 false, Step.rw 1 15 0 false, Step.rw 1 15 1 false, Step.rw 3 14 0 false, Step.mv 14 12,
     Step.mv 15 13, Step.mv 16 14, Step.rw 5 16 1 true, Step.mv 16 15, Step.rw 5 17 1 true, Step.mv 17 16,
     Step.rw 1 17 1 true, Step.rw 2 18 1 true, Step.rw 0 29 0 true, Step.mv 36 21, Step.rw 9 17 1 true,
     Step.rw 1 15 0 true, Step.mv 10 8, Step.mv 17 12, Step.mv 18 13, Step.mv 19 14, Step.mv 20 15, Step.mv 21 16,
     Step.rw 19 7 0 true, Step.mv 7 0, Step.mv 10 9, Step.mv 11 10, Step.rw 5 8 0 true, Step.mv 8 1, Step.rw 1 9 1 true,
     Step.mv 2 0, Step.mv 4 1, Step.mv 4 2, Step.mv 5 3, Step.mv 7 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8,
     Step.mv 13 12, Step.mv 19 16, Step.mv 24 21])
    (by decide +kernel)

/-- Equation 3.101 (supplement: `[ZZ 1 2 D 4 0 1 D 4 1 2]·ω^0 = [D 4 0 1 D 4 1 2 H 0 H 1 ZZ 0 1 H 0 H 1]·ω^0`). -/
theorem rule_3_101 :
    Holds 3 ([Lt.CZ 0] ++ bD 4 1 ++ bD 4 0)
      (bD 4 1 ++ bD 4 0 ++ [.H 2, .H 1, .CZ 1, .H 2, .H 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hL20 db_ok_nil)))
    (steps := [Step.mv 9 1, Step.mv 3 2, Step.mv 6 5, Step.mv 12 11, Step.rw 0 8 1 false, Step.rw 0 13 2 true, Step.rw 0 13 1 true,
     Step.rw 0 2 1 true, Step.rw 0 1 0 true, Step.mv 4 3, Step.mv 5 4, Step.mv 7 5, Step.mv 7 6, Step.mv 10 9, Step.mv 19 12,
     Step.mv 15 14, Step.mv 18 17, Step.rw 2 6 0 true, Step.mv 6 5, Step.mv 8 6, Step.mv 8 7, Step.mv 11 10, Step.mv 14 13,
     Step.mv 16 14, Step.mv 16 15, Step.mv 17 16, Step.mv 20 17, Step.mv 19 18, Step.rw 0 17 0 true, Step.rw 0 8 2 true,
     Step.rw 0 1 0 false, Step.rw 0 1 1 false, Step.rw 1 0 0 false, Step.rw 0 2 2 false, Step.rw 0 11 0 false,
     Step.rw 0 7 1 true, Step.mv 2 0, Step.mv 2 1, Step.mv 3 2, Step.mv 5 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.mv 11 10, Step.mv 15 14, Step.mv 18 17])
    (by decide +kernel)

end QCert.SelingerClifford
