/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): rewrite rules, part 3

Equations 3.41–3.60 of the supplement to Selinger's paper (the rewrite
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

/-- Equation 3.41 (supplement: `[ZZ 1 2 B 2 0 1]·ω^0 = [B 2 0 1 ZZ 0 1 H 1 ZZ 1 2 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_41 :
    Holds 3 ([Lt.CZ 0] ++ bB 2 1)
      (bB 2 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC12 db_ok_nil)))
    (steps := [Step.mv 3 2, Step.rw 1 0 1 true, Step.rw 2 2 0 false, Step.rw 1 0 1 false, Step.rw 0 1 1 true, Step.mv 5 2,
     Step.rw 1 3 1 true, Step.mv 2 1])
    (by decide +kernel)

/-- Equation 3.42 (supplement: `[ZZ 1 2 B 3 0 1]·ω^0 = [B 3 0 1 ZZ 0 1 H 1 ZZ 1 2 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_42 :
    Holds 3 ([Lt.CZ 0] ++ bB 3 1)
      (bB 3 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL9 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 5 4, Step.rw 4 2 1 false, Step.mv 4 3, Step.rw 16 1 1 false, Step.rw 0 15 0 true, Step.mv 22 15, Step.mv 22 16,
     Step.rw 11 11 2 true, Step.mv 22 16, Step.mv 22 17, Step.mv 22 18, Step.mv 22 19, Step.mv 22 20, Step.mv 22 21,
     Step.rw 13 11 2 true, Step.rw 0 19 0 true, Step.mv 26 17, Step.mv 26 18, Step.mv 26 19, Step.mv 26 20,
     Step.rw 12 11 2 true, Step.mv 22 10, Step.rw 9 6 1 true, Step.rw 0 22 0 true, Step.mv 29 9, Step.mv 29 10,
     Step.mv 29 11, Step.mv 29 12, Step.mv 29 13, Step.mv 29 14, Step.mv 29 15, Step.rw 14 6 1 true, Step.mv 26 10,
     Step.rw 9 6 1 true, Step.mv 25 12, Step.rw 10 8 1 true, Step.mv 3 2, Step.mv 4 3, Step.mv 15 7, Step.mv 16 9,
     Step.rw 17 4 1 true, Step.mv 4 2, Step.mv 5 3, Step.mv 6 4, Step.rw 0 21 0 true, Step.mv 28 19, Step.mv 28 20,
     Step.mv 28 21, Step.mv 28 22, Step.rw 12 13 2 true, Step.mv 5 3, Step.mv 6 4, Step.mv 13 8, Step.rw 0 25 0 true,
     Step.mv 32 12, Step.mv 32 13, Step.mv 32 14, Step.mv 32 15, Step.mv 32 16, Step.mv 32 17, Step.mv 32 18,
     Step.rw 7 5 1 true, Step.mv 3 2, Step.mv 4 3, Step.rw 5 4 1 false, Step.mv 10 8, Step.rw 4 7 1 true,
     Step.rw 1 8 2 true, Step.mv 13 11, Step.mv 14 13, Step.rw 15 9 1 true, Step.rw 3 5 0 true, Step.rw 4 6 0 true,
     Step.rw 4 5 0 true, Step.mv 9 6, Step.mv 10 7, Step.mv 11 8, Step.mv 21 9, Step.mv 21 10, Step.mv 21 11, Step.mv 21 12,
     Step.mv 21 13, Step.mv 21 14, Step.mv 21 15, Step.rw 6 2 1 true, Step.rw 8 4 0 true, Step.mv 4 3,
     Step.rw 3 1 1 false, Step.rw 3 0 0 false, Step.rw 2 6 2 true, Step.rw 1 8 2 true, Step.rw 0 13 0 true,
     Step.mv 20 9, Step.mv 20 10, Step.mv 20 11, Step.mv 20 12, Step.mv 20 13, Step.mv 20 14, Step.rw 13 4 2 true,
     Step.rw 2 2 1 true, Step.mv 8 2, Step.mv 9 4, Step.mv 10 6, Step.mv 11 7, Step.rw 15 0 1 true, Step.mv 16 12,
     Step.rw 9 8 2 true, Step.mv 15 14, Step.rw 10 10 2 true, Step.rw 0 15 0 true, Step.mv 22 12, Step.mv 22 13,
     Step.rw 11 8 2 true, Step.mv 8 5, Step.mv 9 6, Step.mv 10 7, Step.rw 0 23 0 true, Step.mv 30 8, Step.mv 30 9,
     Step.mv 30 10, Step.mv 30 11, Step.mv 30 12, Step.mv 30 13, Step.mv 30 14, Step.rw 6 1 1 true, Step.rw 4 0 1 false,
     Step.mv 19 12, Step.mv 19 13, Step.mv 19 14, Step.mv 19 15, Step.mv 19 16, Step.mv 19 17, Step.rw 13 7 2 true,
     Step.rw 0 16 0 true, Step.mv 23 13, Step.mv 23 14, Step.mv 23 15, Step.mv 23 16, Step.rw 12 7 2 true,
     Step.rw 1 4 1 true, Step.rw 2 5 1 true, Step.rw 1 7 1 true, Step.rw 1 1 1 true, Step.mv 3 2, Step.mv 4 3,
     Step.mv 17 7, Step.mv 18 9, Step.rw 17 4 1 true, Step.mv 4 2, Step.mv 5 3, Step.mv 6 4, Step.mv 25 19, Step.mv 25 20,
     Step.rw 11 15 2 true, Step.mv 25 12, Step.mv 25 13, Step.rw 11 8 1 true, Step.mv 5 3, Step.mv 6 4, Step.mv 17 8,
     Step.rw 0 26 0 true, Step.mv 33 12, Step.mv 33 13, Step.mv 33 14, Step.mv 33 15, Step.mv 33 16, Step.mv 33 17,
     Step.mv 33 18, Step.rw 7 5 1 true, Step.mv 3 2, Step.mv 4 3, Step.rw 5 4 1 false, Step.rw 2 8 1 true,
     Step.rw 1 7 2 true, Step.mv 20 10, Step.mv 21 12, Step.mv 22 14, Step.mv 23 15, Step.rw 15 8 1 true, Step.mv 24 16,
     Step.rw 9 12 1 true, Step.mv 23 18, Step.rw 10 14 1 true, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.mv 20 13, Step.mv 21 15, Step.rw 17 10 1 true, Step.mv 10 6, Step.mv 11 7, Step.mv 12 8, Step.rw 5 13 1 true,
     Step.mv 13 9, Step.rw 16 0 1 true, Step.mv 3 2, Step.rw 4 1 1 true, Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.43 (supplement: `[ZZ 1 2 B 4 0 1]·ω^0 = [B 4 0 1 ZZ 0 1 H 1 ZZ 1 2 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_43 :
    Holds 3 ([Lt.CZ 0] ++ bB 4 1)
      (bB 4 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC12 db_ok_nil)))
    (steps := [Step.mv 4 3, Step.rw 1 0 0 true, Step.mv 3 2, Step.rw 2 3 0 false, Step.rw 1 0 0 false, Step.rw 0 2 1 true, Step.mv 6 3,
     Step.rw 1 4 1 true, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.44 (supplement: `[X 0 C 1 0]·ω^0 = [C 2 0]·ω^0`). -/
theorem rule_3_44 :
    Holds 1 (bX 0 ++ bC 1 0)
      (bC 2 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.45 (supplement: `[X 0 C 2 0]·ω^0 = [C 1 0]·ω^0`). -/
theorem rule_3_45 :
    Holds 1 (bX 0 ++ bC 2 0)
      (bC 1 0) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 db_ok_nil))
    (steps := [Step.rw 0 3 0 false, Step.rw 1 1 0 false, Step.rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.46 (supplement: `[S 0 C 1 0]·ω^0 = [C 1 0 S 0]·ω^0`). -/
theorem rule_3_46 :
    Holds 1 ([Lt.S 0] ++ bC 1 0)
      (bC 1 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.47 (supplement: `[S 0 C 2 0]·ω^0 = [C 2 0 S 0 S 0 S 0]·ω^2`). -/
theorem rule_3_47 :
    Holds 1 ([Lt.S 0] ++ bC 2 0)
      (bC 2 0 ++ [.S 0, .S 0, .S 0, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hL9 db_ok_nil))
    (steps := [Step.rw 0 5 0 true, Step.mv 12 5, Step.mv 12 6, Step.mv 12 7, Step.mv 12 8, Step.mv 12 9, Step.mv 12 10, Step.rw 1 0 0 true])
    (by decide +kernel)

/-- Equation 3.48 (supplement: `[ZZ 0 1 C 1 0]·ω^0 = [C 1 0 ZZ 0 1]·ω^0`). -/
theorem rule_3_48 :
    Holds 2 ([Lt.CZ 0] ++ bC 1 1)
      (bC 1 1 ++ [.CZ 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.49 (supplement: `[ZZ 0 1 C 2 0]·ω^0 = [C 2 0 ZZ 0 1 S 1 S 1]·ω^0`). -/
theorem rule_3_49 :
    Holds 2 ([Lt.CZ 0] ++ bC 2 1)
      (bC 2 1 ++ [.CZ 0, .S 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL14 db_ok_nil)))
    (steps := [Step.rw 1 1 0 true, Step.rw 0 0 1 true, Step.mv 7 3, Step.mv 8 5, Step.mv 9 7, Step.mv 10 8, Step.rw 2 1 0 true])
    (by decide +kernel)

/-- Equation 3.50 (supplement: `[ZZ 0 1 B 1 1 2 B 1 0 1]·ω^0 = [B 1 1 2 B 1 0 1 H 1 H 2 ZZ 1 2 H 1 H 2]·ω^0`). -/
theorem rule_3_50 :
    Holds 3 ([Lt.CZ 1] ++ bB 1 0 ++ bB 1 1)
      (bB 1 0 ++ bB 1 1 ++ [.H 1, .H 0, .CZ 0, .H 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 (db_ok_cons hM18 (db_ok_cons hM20 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 1 0, Step.mv 7 6, Step.mv 15 14, Step.mv 1 0, Step.mv 4 3, Step.mv 7 6, Step.rw 16 1 0 false, Step.mv 3 2, Step.mv 6 5,
     Step.rw 1 8 1 false, Step.rw 1 8 2 true, Step.rw 3 9 1 true, Step.rw 1 10 2 true, Step.rw 1 10 1 true,
     Step.mv 12 11, Step.rw 3 12 1 true, Step.rw 1 13 1 true, Step.rw 1 8 0 true, Step.mv 10 4, Step.mv 11 10,
     Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.mv 15 14, Step.rw 17 3 0 true, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.mv 9 8, Step.mv 10 9, Step.rw 2 16 1 true, Step.rw 1 17 1 true, Step.rw 12 10 1 true, Step.rw 2 23 2 true,
     Step.mv 23 16, Step.rw 4 15 1 true, Step.mv 24 17, Step.rw 4 16 1 true, Step.mv 25 18, Step.rw 4 17 1 true,
     Step.rw 2 26 2 true, Step.rw 1 22 1 true, Step.mv 14 13, Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.mv 28 20,
     Step.mv 29 22, Step.rw 13 17 1 true, Step.mv 17 13, Step.mv 18 14, Step.mv 19 15, Step.rw 0 41 0 true,
     Step.mv 48 20, Step.rw 9 16 2 true, Step.mv 16 14, Step.mv 17 15, Step.mv 18 16, Step.mv 47 17, Step.mv 47 18,
     Step.mv 47 19, Step.mv 47 20, Step.mv 47 21, Step.mv 47 22, Step.mv 47 23, Step.rw 5 10 1 true, Step.rw 1 25 2 true,
     Step.rw 0 39 0 true, Step.mv 46 26, Step.rw 8 22 2 true, Step.mv 45 25, Step.mv 45 26, Step.mv 45 27, Step.mv 45 28,
     Step.mv 45 29, Step.mv 45 30, Step.mv 45 31, Step.rw 11 22 2 true, Step.rw 2 18 1 true, Step.rw 1 20 1 true,
     Step.mv 15 13, Step.mv 28 17, Step.mv 29 18, Step.mv 30 19, Step.mv 31 20, Step.mv 32 21, Step.rw 15 12 1 true,
     Step.mv 12 11, Step.mv 15 14, Step.mv 16 15, Step.rw 1 21 1 true, Step.rw 0 43 0 true, Step.mv 50 22, Step.mv 50 23,
     Step.rw 10 18 1 true, Step.mv 16 14, Step.mv 29 19, Step.mv 30 21, Step.rw 0 51 0 true, Step.mv 58 25,
     Step.mv 58 26, Step.mv 58 27, Step.mv 58 28, Step.mv 58 29, Step.mv 58 30, Step.mv 58 31, Step.rw 14 15 1 true,
     Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.mv 17 15, Step.mv 25 19, Step.mv 45 23, Step.mv 45 24, Step.mv 45 25,
     Step.mv 45 26, Step.mv 45 27, Step.mv 45 28, Step.mv 45 29, Step.rw 6 16 1 true, Step.rw 7 18 0 true, Step.mv 20 19,
     Step.mv 22 21, Step.mv 25 24, Step.rw 16 20 1 true, Step.mv 23 22, Step.mv 26 25, Step.rw 1 2 0 true,
     Step.rw 3 4 0 true, Step.mv 7 6, Step.rw 7 5 0 false, Step.rw 1 2 0 false, Step.rw 3 1 0 false,
     Step.rw 3 0 1 false, Step.rw 3 25 1 false, Step.mv 25 24, Step.rw 1 23 1 false, Step.rw 1 23 2 false,
     Step.rw 3 22 1 false, Step.mv 22 21, Step.rw 1 20 1 false, Step.rw 1 20 2 false, Step.rw 3 19 1 false,
     Step.rw 1 8 1 true, Step.mv 2 1, Step.mv 5 4, Step.mv 8 7, Step.rw 16 0 0 true, Step.mv 3 2, Step.mv 6 5, Step.mv 6 5,
     Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 15 13, Step.mv 15 14, Step.mv 16 15,
     Step.mv 17 16, Step.mv 20 19])
    (by decide +kernel)

/-- Equation 3.51 (supplement: `[ZZ 0 1 B 1 1 2 B 2 0 1]·ω^0 = [B 4 1 2 B 2 0 1 H 2 ZZ 1 2 H 2]·ω^0`). -/
theorem rule_3_51 :
    Holds 3 ([Lt.CZ 1] ++ bB 1 0 ++ bB 2 1)
      (bB 4 0 ++ bB 2 1 ++ [.H 0, .CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 1 0, Step.mv 7 6, Step.mv 11 10, Step.mv 1 0, Step.mv 4 3, Step.mv 7 6, Step.rw 17 1 0 false, Step.mv 3 2, Step.mv 6 5,
     Step.rw 1 8 0 true, Step.mv 9 14, Step.rw 3 14 0 true, Step.rw 3 15 1 true, Step.rw 1 15 0 true,
     Step.rw 1 0 1 true, Step.rw 3 1 0 true, Step.rw 1 2 1 true, Step.rw 7 6 0 true, Step.mv 8 7,
     Step.rw 6 4 0 false, Step.mv 17 37, Step.mv 16 36, Step.mv 15 35, Step.mv 14 34, Step.mv 13 33, Step.mv 12 32,
     Step.mv 11 31, Step.mv 11 8, Step.rw 12 3 0 false, Step.mv 19 43, Step.mv 18 42, Step.mv 17 41, Step.mv 16 40,
     Step.mv 15 39, Step.mv 14 38, Step.mv 13 37, Step.rw 0 43 0 false, Step.mv 7 6, Step.mv 9 7, Step.mv 13 8, Step.mv 14 9,
     Step.rw 9 10 1 false, Step.mv 15 36, Step.mv 14 35, Step.rw 0 35 0 false, Step.rw 1 13 1 false, Step.mv 29 27,
     Step.rw 7 26 0 false, Step.rw 3 25 1 false, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.rw 5 13 1 false,
     Step.rw 13 14 0 false, Step.rw 1 21 0 false, Step.rw 5 12 1 false, Step.rw 13 13 0 false,
     Step.rw 1 20 0 false, Step.rw 5 11 1 false, Step.rw 13 12 0 false, Step.rw 1 19 0 false, Step.mv 10 7,
     Step.mv 11 8, Step.mv 12 9, Step.rw 15 10 0 false, Step.mv 10 7, Step.mv 14 13, Step.mv 16 14, Step.mv 17 15,
     Step.mv 18 16, Step.rw 1 15 0 false, Step.rw 11 15 0 false, Step.mv 18 17, Step.mv 20 18, Step.mv 23 19,
     Step.mv 24 20, Step.mv 25 21, Step.mv 26 22, Step.rw 1 26 1 false, Step.mv 15 14, Step.rw 5 15 0 false,
     Step.rw 10 16 0 false, Step.mv 25 37, Step.mv 24 36, Step.mv 23 35, Step.mv 22 34, Step.mv 21 33, Step.mv 20 32,
     Step.mv 19 31, Step.mv 14 13, Step.rw 5 14 0 false, Step.rw 8 15 0 false, Step.mv 19 31, Step.rw 0 31 0 false,
     Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 13 12, Step.rw 16 9 0 false, Step.mv 9 6, Step.mv 12 11, Step.mv 17 14,
     Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.rw 1 20 1 false, Step.rw 5 21 1 false, Step.rw 5 20 1 false,
     Step.rw 11 21 0 false, Step.mv 24 23, Step.mv 26 24, Step.mv 29 25, Step.mv 30 26, Step.rw 5 19 1 false,
     Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.rw 5 21 0 false, Step.mv 17 16, Step.mv 18 17,
     Step.mv 19 18, Step.mv 20 19, Step.rw 5 20 0 false, Step.rw 2 21 0 false, Step.mv 16 15, Step.mv 17 16,
     Step.mv 18 17, Step.mv 19 18, Step.rw 5 19 0 false, Step.mv 7 6, Step.mv 12 11, Step.mv 15 14, Step.rw 14 5 0 false,
     Step.mv 6 2, Step.mv 9 8, Step.mv 11 9, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13, Step.mv 17 14,
     Step.rw 1 5 1 false, Step.rw 2 7 0 false, Step.rw 1 6 0 false, Step.rw 1 9 1 false, Step.rw 4 4 0 false,
     Step.mv 6 5, Step.rw 5 6 1 false, Step.rw 2 7 1 false, Step.mv 3 2, Step.mv 6 5, Step.mv 8 6, Step.mv 8 7, Step.mv 9 8])
    (by decide +kernel)

/-- Equation 3.52 (supplement: `[ZZ 0 1 B 1 1 2 B 3 0 1]·ω^0 = [B 4 1 2 B 3 0 1 H 2 H 1 S 1 H 1 ZZ 2 1 S 1 H 1 S 1 H 2]·ω^7`). -/
theorem rule_3_52 :
    Holds 3 ([Lt.CZ 1] ++ bB 1 0 ++ bB 3 1)
      (bB 4 0 ++ bB 3 1 ++ [.H 0, .H 1, .S 1, .H 1, .CZ 0, .S 1, .H 1, .S 1, .H 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil))))))))))))))))))))
    (steps := [Step.mv 1 0, Step.mv 7 6, Step.mv 13 12, Step.rw 4 10 1 false, Step.mv 12 11, Step.rw 15 9 1 false, Step.mv 1 0, Step.mv 4 3,
     Step.mv 7 6, Step.rw 19 1 0 false, Step.mv 3 2, Step.mv 6 5, Step.rw 1 8 0 true, Step.mv 9 15, Step.rw 3 15 0 true,
     Step.rw 3 16 1 true, Step.rw 1 16 2 true, Step.rw 2 17 2 true, Step.rw 1 19 2 true, Step.rw 2 15 1 true,
     Step.rw 2 15 1 true, Step.rw 1 18 1 true, Step.rw 2 19 1 true, Step.rw 1 0 1 true, Step.rw 3 1 0 true,
     Step.rw 1 2 1 true, Step.rw 1 2 0 true, Step.rw 11 23 1 false, Step.mv 32 61, Step.mv 31 60, Step.mv 30 59,
     Step.mv 29 58, Step.mv 28 57, Step.mv 27 56, Step.mv 26 55, Step.rw 8 23 1 false, Step.mv 27 55,
     Step.rw 0 55 0 false, Step.rw 1 26 1 false, Step.rw 2 23 1 false, Step.rw 2 23 1 false,
     Step.rw 1 27 2 false, Step.rw 2 25 2 false, Step.mv 24 23, Step.mv 25 24, Step.rw 1 23 2 false,
     Step.rw 7 8 0 true, Step.mv 10 9, Step.rw 6 6 0 false, Step.mv 19 47, Step.mv 18 46, Step.mv 17 45, Step.mv 16 44,
     Step.mv 15 43, Step.mv 14 42, Step.mv 13 41, Step.mv 13 10, Step.rw 13 5 0 false, Step.mv 21 53, Step.mv 20 52,
     Step.mv 19 51, Step.mv 18 50, Step.mv 17 49, Step.mv 16 48, Step.mv 15 47, Step.rw 0 53 0 false, Step.mv 9 8,
     Step.mv 11 9, Step.mv 15 10, Step.mv 16 11, Step.rw 10 12 1 false, Step.mv 17 46, Step.mv 16 45,
     Step.rw 0 45 0 false, Step.rw 1 15 1 false, Step.rw 7 29 0 false, Step.rw 3 28 1 false, Step.mv 28 26,
     Step.rw 5 15 1 false, Step.rw 14 16 0 false, Step.rw 1 23 0 false, Step.rw 5 14 1 false,
     Step.rw 14 15 0 false, Step.rw 1 22 0 false, Step.rw 5 13 1 false, Step.rw 14 14 0 false,
     Step.rw 1 21 0 false, Step.mv 12 9, Step.mv 13 10, Step.mv 14 11, Step.rw 17 12 0 false, Step.mv 12 9,
     Step.mv 16 15, Step.mv 18 16, Step.mv 19 17, Step.mv 20 18, Step.rw 1 17 0 false, Step.rw 12 17 0 false,
     Step.mv 20 19, Step.mv 22 20, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.rw 1 28 1 false,
     Step.mv 17 16, Step.rw 5 17 0 false, Step.rw 11 18 0 false, Step.mv 27 47, Step.mv 26 46, Step.mv 25 45,
     Step.mv 24 44, Step.mv 23 43, Step.mv 22 42, Step.mv 21 41, Step.mv 16 15, Step.rw 5 16 0 false,
     Step.rw 9 17 0 false, Step.mv 21 41, Step.rw 0 41 0 false, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.mv 15 14,
     Step.rw 18 11 0 false, Step.mv 11 8, Step.mv 14 13, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19,
     Step.rw 1 22 1 false, Step.rw 5 23 1 false, Step.rw 5 22 1 false, Step.rw 12 23 0 false, Step.mv 26 25,
     Step.mv 28 26, Step.rw 5 21 1 false, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22,
     Step.rw 5 23 0 false, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.rw 5 22 0 false,
     Step.rw 2 23 0 false, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.rw 5 21 0 false, Step.mv 9 8,
     Step.mv 14 13, Step.mv 17 16, Step.rw 16 7 0 false, Step.mv 8 4, Step.mv 11 10, Step.mv 13 11, Step.mv 15 12,
     Step.mv 16 13, Step.mv 17 14, Step.rw 1 2 0 false, Step.rw 1 5 1 false, Step.rw 2 7 0 false,
     Step.rw 1 9 1 false, Step.rw 4 4 0 false, Step.mv 6 5, Step.rw 5 6 1 false, Step.rw 2 7 1 false, Step.mv 13 12,
     Step.rw 4 11 0 true, Step.mv 14 13, Step.rw 4 12 0 true, Step.rw 1 13 1 true, Step.rw 2 14 1 true,
     Step.rw 0 28 0 true, Step.mv 35 17, Step.rw 9 13 1 true, Step.mv 24 16, Step.mv 25 17, Step.mv 26 18, Step.mv 27 19,
     Step.rw 15 6 1 true, Step.mv 9 8, Step.rw 4 7 1 true, Step.mv 3 2, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 10 8,
     Step.mv 10 9, Step.mv 11 10, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18])
    (by decide +kernel)

/-- Equation 3.53 (supplement: `[ZZ 0 1 B 1 1 2 B 4 0 1]·ω^0 = [B 1 1 2 B 4 0 1 H 1 H 2 ZZ 1 2 H 1 H 2]·ω^0`). -/
theorem rule_3_53 :
    Holds 3 ([Lt.CZ 1] ++ bB 1 0 ++ bB 4 1)
      (bB 1 0 ++ bB 4 1 ++ [.H 1, .H 0, .CZ 0, .H 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hL18 (db_ok_cons hL20 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil)))))))))))))))))))
    (steps := [Step.mv 1 0, Step.mv 7 6, Step.mv 12 11, Step.mv 1 0, Step.mv 4 3, Step.mv 7 6, Step.rw 18 1 0 false, Step.mv 3 2, Step.mv 6 5,
     Step.rw 1 0 2 true, Step.rw 3 0 0 true, Step.mv 1 2, Step.rw 1 1 1 true, Step.mv 2 3, Step.rw 1 1 0 true,
     Step.mv 2 4, Step.rw 3 3 0 true, Step.mv 4 5, Step.rw 1 4 1 true, Step.mv 5 6, Step.rw 1 4 0 true, Step.mv 5 7,
     Step.rw 3 6 0 true, Step.mv 7 8, Step.rw 1 7 1 true, Step.mv 8 9, Step.rw 3 9 1 true, Step.rw 1 10 2 true,
     Step.rw 1 10 1 true, Step.mv 11 12, Step.rw 3 12 1 true, Step.rw 1 13 1 true, Step.rw 1 7 0 true, Step.mv 8 15,
     Step.rw 3 15 0 true, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22,
     Step.mv 26 25, Step.mv 29 28, Step.rw 18 23 0 false, Step.mv 25 24, Step.mv 28 27, Step.rw 15 22 0 false,
     Step.mv 30 29, Step.mv 31 30, Step.mv 32 31, Step.mv 35 34, Step.mv 38 37, Step.rw 18 32 0 false, Step.mv 34 33,
     Step.mv 37 36, Step.rw 1 39 1 false, Step.rw 7 31 0 true, Step.mv 31 30, Step.mv 33 31, Step.rw 5 28 0 false,
     Step.mv 41 54, Step.mv 40 53, Step.mv 39 52, Step.mv 38 51, Step.mv 37 50, Step.mv 36 49, Step.mv 35 48, Step.mv 35 32,
     Step.rw 13 27 0 false, Step.mv 43 60, Step.mv 42 59, Step.mv 41 58, Step.mv 40 57, Step.mv 39 56, Step.mv 38 55,
     Step.mv 37 54, Step.rw 0 60 0 false, Step.mv 31 30, Step.mv 33 31, Step.mv 37 32, Step.mv 38 33,
     Step.rw 10 34 1 false, Step.mv 39 53, Step.mv 38 52, Step.rw 0 52 0 false, Step.rw 1 37 1 false,
     Step.rw 14 24 0 false, Step.mv 38 34, Step.mv 39 35, Step.mv 40 36, Step.mv 41 37, Step.rw 11 29 0 false,
     Step.mv 38 60, Step.mv 37 59, Step.mv 36 58, Step.mv 35 57, Step.mv 34 56, Step.mv 33 55, Step.mv 32 54,
     Step.rw 8 29 0 false, Step.mv 33 54, Step.rw 0 54 0 false, Step.rw 1 32 0 false, Step.rw 1 35 1 false,
     Step.rw 2 33 1 false, Step.rw 6 22 0 false, Step.mv 35 56, Step.mv 34 55, Step.mv 33 54, Step.mv 32 53,
     Step.mv 31 52, Step.mv 30 51, Step.mv 29 50, Step.mv 22 17, Step.mv 23 18, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27,
     Step.mv 29 28, Step.rw 9 25 0 false, Step.mv 29 50, Step.rw 0 50 0 false, Step.mv 29 28, Step.mv 30 29,
     Step.mv 31 30, Step.rw 4 31 0 false, Step.rw 2 32 0 false, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29,
     Step.rw 4 30 0 false, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.rw 4 29 0 false, Step.rw 12 26 0 false,
     Step.mv 29 28, Step.mv 31 29, Step.mv 34 30, Step.mv 35 31, Step.rw 2 28 0 false, Step.rw 1 31 1 false,
     Step.mv 19 17, Step.mv 20 18, Step.mv 21 19, Step.mv 22 20, Step.mv 23 21, Step.mv 26 25, Step.rw 17 22 0 false,
     Step.mv 22 17, Step.mv 25 24, Step.rw 1 29 1 false, Step.rw 2 28 1 false, Step.mv 18 17, Step.mv 21 20,
     Step.mv 28 23, Step.mv 26 25, Step.rw 16 16 0 false, Step.mv 17 16, Step.mv 20 19, Step.mv 23 22, Step.mv 25 23,
     Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29, Step.mv 31 30, Step.mv 32 31,
     Step.rw 1 26 1 false, Step.mv 30 22, Step.mv 31 23, Step.rw 1 22 2 false, Step.rw 3 25 0 false, Step.mv 25 24,
     Step.rw 1 23 0 false, Step.rw 1 23 1 false, Step.rw 3 22 0 false, Step.rw 3 21 1 false, Step.mv 21 20,
     Step.rw 1 19 1 false, Step.rw 1 19 2 false, Step.rw 3 18 1 false, Step.mv 2 1, Step.mv 5 4, Step.mv 8 7,
     Step.rw 18 0 0 true, Step.mv 3 2, Step.mv 6 5, Step.mv 6 5, Step.mv 9 8, Step.mv 10 9, Step.mv 12 10, Step.mv 12 11,
     Step.mv 13 12, Step.mv 14 13, Step.mv 17 16])
    (by decide +kernel)

/-- Equation 3.54 (supplement: `[ZZ 0 1 B 2 1 2 B 1 0 1]·ω^0 = [B 2 1 2 B 4 0 1 H 1 ZZ 1 2 H 1]·ω^0`). -/
theorem rule_3_54 :
    Holds 3 ([Lt.CZ 1] ++ bB 2 0 ++ bB 1 1)
      (bB 2 0 ++ bB 4 1 ++ [.H 1, .CZ 0, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 11 10, Step.mv 8 7, Step.mv 11 10, Step.rw 15 5 1 false, Step.mv 7 6, Step.mv 10 9, Step.rw 1 12 1 true,
     Step.mv 13 14, Step.rw 3 13 0 true, Step.mv 14 15, Step.rw 1 14 1 true, Step.mv 15 16, Step.rw 3 16 1 true,
     Step.rw 3 0 0 true, Step.rw 1 1 1 true, Step.rw 1 1 0 true, Step.mv 2 3, Step.rw 3 3 0 true, Step.rw 7 8 0 true,
     Step.mv 10 9, Step.rw 3 7 0 false, Step.mv 7 6, Step.rw 1 5 0 false, Step.rw 7 8 0 false, Step.rw 6 6 1 false,
     Step.mv 19 35, Step.mv 18 34, Step.mv 17 33, Step.mv 16 32, Step.mv 15 31, Step.mv 14 30, Step.mv 13 29, Step.mv 10 9,
     Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.rw 13 5 1 false, Step.mv 21 41, Step.mv 20 40,
     Step.mv 19 39, Step.mv 18 38, Step.mv 17 37, Step.mv 16 36, Step.mv 15 35, Step.rw 0 41 0 false, Step.mv 10 9,
     Step.mv 12 10, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.mv 16 14, Step.mv 17 15, Step.mv 18 16, Step.mv 19 17,
     Step.rw 8 8 1 false, Step.mv 13 34, Step.mv 12 33, Step.rw 0 33 0 false, Step.rw 1 11 1 false,
     Step.rw 4 11 0 false, Step.rw 4 10 0 false, Step.rw 4 9 0 false, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13,
     Step.mv 17 14, Step.rw 12 15 1 false, Step.mv 15 11, Step.mv 19 18, Step.mv 21 19, Step.mv 22 20, Step.mv 23 21,
     Step.rw 1 20 1 false, Step.rw 10 13 1 false, Step.mv 16 15, Step.mv 18 16, Step.mv 21 17, Step.mv 22 18,
     Step.mv 23 19, Step.rw 9 21 2 false, Step.mv 30 40, Step.mv 29 39, Step.mv 28 38, Step.mv 27 37, Step.mv 20 15,
     Step.mv 21 16, Step.rw 1 15 2 false, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23,
     Step.rw 5 24 1 false, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22,
     Step.rw 5 23 1 false, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19,
     Step.rw 12 20 1 false, Step.mv 20 15, Step.mv 24 23, Step.mv 26 24, Step.mv 27 25, Step.mv 28 26, Step.mv 29 27,
     Step.mv 30 28, Step.mv 31 29, Step.mv 32 30, Step.rw 9 23 1 false, Step.mv 32 42, Step.mv 31 41, Step.mv 30 40,
     Step.mv 29 39, Step.rw 0 39 0 false, Step.rw 1 22 1 false, Step.rw 4 20 1 false, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.rw 4 19 1 false, Step.mv 21 20,
     Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 27 20, Step.mv 28 21,
     Step.mv 29 22, Step.mv 30 23, Step.rw 2 20 2 false, Step.rw 10 16 1 false, Step.mv 19 18, Step.mv 21 19,
     Step.mv 24 20, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26,
     Step.rw 2 18 1 false, Step.rw 1 26 2 false, Step.mv 12 10, Step.mv 13 11, Step.mv 16 15, Step.rw 14 12 1 false,
     Step.mv 12 10, Step.mv 15 14, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20, Step.mv 24 21,
     Step.rw 1 24 2 false, Step.rw 11 11 1 false, Step.rw 1 18 1 false, Step.rw 4 19 0 false,
     Step.rw 4 18 0 false, Step.rw 4 17 0 false, Step.mv 22 19, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22,
     Step.rw 12 23 1 false, Step.mv 23 19, Step.mv 27 26, Step.mv 29 27, Step.mv 30 28, Step.rw 4 23 1 false,
     Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.rw 4 22 1 false, Step.mv 24 23, Step.mv 25 24,
     Step.mv 26 25, Step.mv 27 26, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26, Step.rw 2 23 2 false,
     Step.rw 4 21 1 false, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 11 9, Step.mv 20 17,
     Step.rw 16 7 0 false, Step.mv 12 11, Step.mv 14 12, Step.mv 17 13, Step.mv 18 14, Step.mv 19 15, Step.mv 20 16,
     Step.rw 1 6 1 false, Step.rw 1 10 1 false, Step.rw 2 14 2 false, Step.mv 6 5, Step.rw 5 6 1 false,
     Step.rw 4 7 0 false, Step.rw 2 8 1 false, Step.rw 7 6 0 true, Step.mv 6 5, Step.rw 3 3 0 false, Step.mv 2 1,
     Step.mv 7 6])
    (by decide +kernel)

/-- Equation 3.55 (supplement: `[ZZ 0 1 B 2 1 2 B 2 0 1]·ω^0 = [B 3 1 2 B 3 0 1 H 1 S 1 H 1 H 2 S 2 H 2 ZZ 1 2 S 1 S 2]·ω^6`). -/
theorem rule_3_55 :
    Holds 3 ([Lt.CZ 1] ++ bB 2 0 ++ bB 2 1)
      (bB 3 0 ++ bB 3 1 ++ [.H 1, .S 1, .H 1, .H 0, .S 0, .H 0, .CZ 0, .S 1, .S 0, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 7 6, Step.rw 3 7 0 true, Step.mv 9 8, Step.rw 8 9 0 false, Step.rw 2 11 1 true, Step.rw 4 10 0 true,
     Step.rw 2 12 0 true, Step.rw 5 11 0 true, Step.mv 11 8, Step.rw 5 10 1 true, Step.mv 10 9, Step.rw 1 9 1 true,
     Step.rw 2 10 1 true, Step.rw 1 12 1 true, Step.rw 2 8 0 true, Step.mv 13 8, Step.mv 14 10, Step.mv 15 12,
     Step.mv 16 13, Step.rw 13 6 0 true, Step.rw 0 27 0 true, Step.mv 34 17, Step.mv 34 18, Step.rw 11 13 1 true,
     Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.rw 0 35 0 true, Step.mv 42 14, Step.mv 42 15, Step.mv 42 16,
     Step.mv 42 17, Step.mv 42 18, Step.mv 42 19, Step.mv 42 20, Step.rw 6 7 0 true, Step.rw 4 6 0 false,
     Step.rw 1 16 1 true, Step.mv 12 10, Step.mv 13 12, Step.mv 33 17, Step.mv 33 18, Step.mv 33 19, Step.mv 33 20,
     Step.mv 33 21, Step.mv 33 22, Step.mv 33 23, Step.rw 14 7 0 true, Step.rw 3 5 1 true, Step.rw 8 7 0 true,
     Step.rw 2 14 2 true, Step.rw 0 27 0 true, Step.mv 34 12, Step.mv 34 13, Step.mv 34 14, Step.mv 34 15, Step.mv 34 16,
     Step.mv 34 17, Step.mv 34 18, Step.rw 12 9 1 true, Step.mv 31 13, Step.rw 9 9 1 true, Step.rw 0 31 0 true,
     Step.mv 38 15, Step.rw 10 11 1 true, Step.rw 1 8 1 true, Step.mv 20 12, Step.mv 21 14, Step.rw 16 9 1 true,
     Step.mv 18 13, Step.mv 35 17, Step.mv 35 18, Step.mv 35 19, Step.mv 35 20, Step.mv 35 21, Step.mv 35 22, Step.mv 35 23,
     Step.rw 7 10 1 true, Step.rw 8 12 0 true, Step.rw 5 9 1 false, Step.rw 1 8 0 true, Step.mv 10 9,
     Step.rw 3 10 0 true, Step.mv 13 12, Step.rw 8 11 0 false, Step.rw 3 5 1 false, Step.rw 3 4 0 false, Step.mv 4 3,
     Step.rw 1 2 0 false, Step.rw 1 2 1 false, Step.rw 3 1 0 false, Step.rw 3 0 1 false, Step.mv 14 11,
     Step.rw 4 10 0 true, Step.mv 15 12, Step.rw 4 11 0 true, Step.rw 1 17 2 true, Step.rw 2 18 2 true,
     Step.rw 1 20 2 true, Step.rw 1 12 1 true, Step.rw 2 13 1 true, Step.rw 0 31 0 true, Step.mv 38 16,
     Step.rw 10 12 1 true, Step.mv 23 15, Step.mv 24 16, Step.mv 25 17, Step.mv 26 18, Step.rw 15 5 1 true,
     Step.mv 29 14, Step.mv 29 15, Step.mv 29 16, Step.mv 29 17, Step.mv 29 18, Step.mv 29 19, Step.mv 29 20,
     Step.rw 12 11 1 true, Step.mv 23 11, Step.mv 24 13, Step.mv 25 15, Step.mv 26 16, Step.rw 13 9 1 true,
     Step.rw 5 18 0 true, Step.mv 18 5, Step.rw 5 19 0 true, Step.mv 19 6, Step.rw 5 14 1 true, Step.mv 14 10,
     Step.rw 0 23 0 true, Step.mv 30 20, Step.rw 10 16 1 true, Step.rw 5 15 1 true, Step.mv 15 11, Step.mv 12 9,
     Step.rw 4 8 1 true, Step.rw 1 13 1 true, Step.rw 1 7 1 true, Step.mv 9 8, Step.mv 10 9, Step.mv 17 13,
     Step.mv 18 15, Step.rw 16 10 1 true, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.rw 1 7 0 true,
     Step.rw 2 8 0 true, Step.mv 35 11, Step.rw 10 7 0 true, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13,
     Step.rw 15 0 0 true, Step.mv 3 2, Step.rw 4 1 0 true, Step.mv 4 3, Step.mv 9 6, Step.mv 10 7, Step.mv 11 8,
     Step.mv 13 9, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13, Step.mv 17 14, Step.mv 20 19])
    (by decide +kernel)

/-- Equation 3.56 (supplement: `[ZZ 0 1 B 2 1 2 B 3 0 1]·ω^0 = [B 3 1 2 B 2 0 1 H 2 S 2 H 2 ZZ 1 2 X 0 H 1 S 1 S 2]·ω^7`). -/
theorem rule_3_56 :
    Holds 3 ([Lt.CZ 1] ++ bB 2 0 ++ bB 3 1)
      (bB 3 0 ++ bB 2 1 ++ [.H 0, .S 0, .H 0, .CZ 0] ++ bX 2 ++ [.H 1, .S 1, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 9 8, Step.rw 4 6 1 false, Step.mv 8 7, Step.rw 15 5 1 false, Step.rw 3 7 0 true, Step.mv 9 8,
     Step.mv 10 9, Step.rw 8 10 0 false, Step.rw 4 11 0 true, Step.rw 4 12 0 true, Step.rw 4 13 0 true,
     Step.rw 2 18 2 true, Step.rw 1 20 2 true, Step.mv 17 11, Step.mv 18 13, Step.mv 19 15, Step.mv 20 16,
     Step.rw 13 9 1 true, Step.rw 2 15 0 true, Step.rw 5 14 0 true, Step.mv 14 8, Step.rw 5 13 1 true, Step.mv 13 9,
     Step.rw 1 9 1 true, Step.rw 2 10 1 true, Step.rw 1 12 1 true, Step.rw 2 8 0 true, Step.mv 13 8, Step.mv 14 10,
     Step.mv 15 12, Step.mv 16 13, Step.rw 13 6 0 true, Step.rw 0 35 0 true, Step.mv 42 17, Step.mv 42 18,
     Step.rw 11 13 1 true, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.rw 0 43 0 true, Step.mv 50 14,
     Step.mv 50 15, Step.mv 50 16, Step.mv 50 17, Step.mv 50 18, Step.mv 50 19, Step.mv 50 20, Step.rw 6 7 0 true,
     Step.rw 4 6 0 false, Step.rw 1 16 1 true, Step.mv 12 10, Step.mv 13 12, Step.mv 41 17, Step.mv 41 18, Step.mv 41 19,
     Step.mv 41 20, Step.mv 41 21, Step.mv 41 22, Step.mv 41 23, Step.rw 14 7 0 true, Step.rw 3 5 1 true,
     Step.rw 8 7 0 true, Step.rw 0 31 0 true, Step.mv 38 12, Step.mv 38 13, Step.mv 38 14, Step.mv 38 15, Step.mv 38 16,
     Step.mv 38 17, Step.mv 38 18, Step.rw 12 9 1 true, Step.mv 35 13, Step.rw 9 9 1 true, Step.rw 0 35 0 true,
     Step.mv 42 15, Step.rw 10 11 1 true, Step.rw 1 8 1 true, Step.mv 20 12, Step.mv 21 14, Step.rw 16 9 1 true,
     Step.mv 18 13, Step.mv 39 17, Step.mv 39 18, Step.mv 39 19, Step.mv 39 20, Step.mv 39 21, Step.mv 39 22, Step.mv 39 23,
     Step.rw 7 10 1 true, Step.rw 8 12 0 true, Step.rw 5 9 1 false, Step.rw 1 8 0 true, Step.mv 10 9,
     Step.rw 3 10 0 true, Step.mv 13 12, Step.rw 8 11 0 false, Step.rw 3 5 1 false, Step.rw 3 4 0 false, Step.mv 4 3,
     Step.rw 1 2 0 false, Step.rw 1 2 1 false, Step.rw 3 1 0 false, Step.rw 3 0 1 false, Step.rw 2 16 2 false,
     Step.rw 1 15 2 false, Step.rw 1 15 2 true, Step.rw 2 16 2 true, Step.rw 1 18 2 true, Step.rw 2 9 1 true,
     Step.mv 19 9, Step.mv 20 11, Step.mv 21 13, Step.mv 22 14, Step.rw 13 7 1 true, Step.rw 5 13 0 true, Step.mv 13 5,
     Step.rw 5 14 0 true, Step.mv 14 6, Step.rw 5 12 1 true, Step.mv 12 9, Step.rw 5 13 1 true, Step.mv 13 10,
     Step.rw 1 11 1 true, Step.rw 1 7 1 true, Step.mv 15 11, Step.mv 16 13, Step.rw 16 8 1 true, Step.rw 1 7 0 true,
     Step.rw 2 8 0 true, Step.rw 0 29 0 true, Step.mv 36 11, Step.rw 10 7 0 true, Step.mv 13 10, Step.mv 14 11,
     Step.mv 15 12, Step.mv 16 13, Step.rw 15 0 0 true, Step.mv 3 2, Step.rw 4 1 0 true, Step.mv 4 3, Step.mv 9 6,
     Step.mv 11 7, Step.mv 11 8, Step.mv 12 9, Step.mv 17 14, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.mv 19 18,
     Step.mv 20 19])
    (by decide +kernel)

/-- Equation 3.57 (supplement: `[ZZ 0 1 B 2 1 2 B 4 0 1]·ω^0 = [B 2 1 2 B 1 0 1 H 1 ZZ 1 2 H 1]·ω^0`). -/
theorem rule_3_57 :
    Holds 3 ([Lt.CZ 1] ++ bB 2 0 ++ bB 4 1)
      (bB 2 0 ++ bB 1 1 ++ [.H 1, .CZ 0, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 8 7, Step.rw 3 4 0 true, Step.mv 7 6, Step.rw 7 7 0 false, Step.rw 2 9 1 true, Step.rw 4 8 0 true,
     Step.rw 5 7 1 true, Step.mv 7 6, Step.rw 2 15 2 true, Step.rw 1 11 1 true, Step.rw 1 7 1 true, Step.mv 18 12,
     Step.mv 19 14, Step.mv 20 16, Step.mv 21 17, Step.rw 16 8 0 true, Step.mv 11 10, Step.mv 12 11, Step.mv 19 18,
     Step.mv 20 19, Step.mv 21 20, Step.mv 27 23, Step.rw 4 22 1 true, Step.rw 2 28 2 true, Step.mv 28 24,
     Step.rw 4 23 1 true, Step.mv 29 25, Step.rw 4 24 1 true, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23,
     Step.mv 30 27, Step.mv 31 29, Step.rw 12 24 1 true, Step.mv 24 20, Step.mv 25 21, Step.mv 26 22,
     Step.rw 4 18 0 true, Step.rw 4 19 0 true, Step.rw 4 20 0 true, Step.rw 1 19 1 true, Step.rw 11 12 1 true,
     Step.rw 1 25 2 true, Step.mv 12 11, Step.mv 13 12, Step.mv 16 15, Step.mv 23 18, Step.mv 24 19, Step.mv 25 20,
     Step.rw 14 13 1 true, Step.mv 13 11, Step.mv 14 12, Step.mv 17 16, Step.rw 1 27 2 true, Step.rw 2 19 1 true,
     Step.mv 28 19, Step.mv 29 21, Step.mv 30 23, Step.mv 31 24, Step.rw 10 17 1 true, Step.rw 2 28 2 true,
     Step.mv 28 21, Step.rw 4 20 1 true, Step.mv 29 22, Step.rw 4 21 1 true, Step.rw 1 23 1 true,
     Step.rw 0 37 0 true, Step.mv 44 30, Step.mv 44 31, Step.mv 44 32, Step.mv 44 33, Step.rw 9 24 1 true, Step.mv 17 16,
     Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 32 24, Step.mv 33 26, Step.rw 12 21 1 true,
     Step.mv 21 16, Step.mv 22 17, Step.mv 23 18, Step.rw 5 24 1 true, Step.mv 24 19, Step.rw 5 25 1 true, Step.mv 25 20,
     Step.rw 1 21 2 true, Step.mv 38 28, Step.mv 38 29, Step.mv 38 30, Step.mv 38 31, Step.rw 9 22 2 true, Step.mv 21 16,
     Step.mv 22 18, Step.mv 23 20, Step.mv 24 21, Step.rw 10 14 1 true, Step.rw 1 21 1 true, Step.mv 13 12,
     Step.mv 14 13, Step.mv 15 14, Step.mv 16 15, Step.mv 23 19, Step.mv 24 21, Step.rw 12 16 1 true, Step.mv 16 12,
     Step.mv 17 13, Step.mv 18 14, Step.rw 4 10 0 true, Step.rw 4 11 0 true, Step.rw 4 12 0 true,
     Step.rw 1 12 1 true, Step.rw 0 31 0 true, Step.mv 38 13, Step.mv 38 14, Step.rw 8 9 1 true, Step.mv 19 10,
     Step.mv 20 12, Step.rw 0 39 0 true, Step.mv 46 16, Step.mv 46 17, Step.mv 46 18, Step.mv 46 19, Step.mv 46 20,
     Step.mv 46 21, Step.mv 46 22, Step.rw 13 6 1 true, Step.mv 15 10, Step.mv 33 14, Step.mv 33 15, Step.mv 33 16,
     Step.mv 33 17, Step.mv 33 18, Step.mv 33 19, Step.mv 33 20, Step.rw 6 7 1 true, Step.rw 7 9 0 true,
     Step.rw 1 6 0 true, Step.mv 8 7, Step.rw 3 8 0 true, Step.mv 11 10, Step.rw 7 9 0 false, Step.rw 3 4 0 false,
     Step.mv 4 3, Step.rw 1 2 0 false, Step.rw 1 2 1 false, Step.rw 3 1 0 false, Step.rw 3 0 1 false,
     Step.rw 3 15 1 false, Step.mv 6 5, Step.mv 9 8, Step.mv 14 11, Step.rw 15 4 1 true, Step.mv 7 6, Step.mv 10 9,
     Step.mv 2 1, Step.mv 10 9])
    (by decide +kernel)

/-- Equation 3.58 (supplement: `[ZZ 0 1 B 3 1 2 B 1 0 1]·ω^0 = [B 3 1 2 B 4 0 1 H 1 H 2 S 2 H 2 ZZ 1 2 H 1 S 2 H 2 S 2]·ω^7`). -/
theorem rule_3_58 :
    Holds 3 ([Lt.CZ 1] ++ bB 3 0 ++ bB 1 1)
      (bB 3 0 ++ bB 4 1 ++ [.H 1, .H 0, .S 0, .H 0, .CZ 0, .H 1, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))))))
    (steps := [Step.mv 5 4, Step.mv 13 12, Step.rw 4 2 0 false, Step.mv 4 3, Step.rw 15 1 0 false, Step.rw 1 14 1 false,
     Step.rw 5 13 1 false, Step.rw 5 12 1 false, Step.mv 16 13, Step.rw 16 14 1 false, Step.mv 14 13, Step.mv 18 17,
     Step.mv 20 18, Step.mv 21 19, Step.mv 22 20, Step.rw 1 19 1 false, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20,
     Step.rw 5 21 1 false, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.rw 5 20 1 false, Step.rw 13 17 1 false,
     Step.mv 20 19, Step.mv 22 20, Step.mv 25 21, Step.mv 26 22, Step.rw 2 19 1 false, Step.mv 14 13, Step.mv 17 16,
     Step.rw 19 11 1 false, Step.mv 13 12, Step.mv 16 15, Step.rw 1 18 2 false, Step.mv 11 6, Step.mv 12 7, Step.mv 13 8,
     Step.mv 14 9, Step.mv 15 10, Step.mv 16 11, Step.mv 17 12, Step.rw 1 13 2 true, Step.mv 14 19, Step.rw 1 13 1 true,
     Step.mv 14 20, Step.rw 3 14 0 true, Step.mv 15 16, Step.rw 1 15 1 true, Step.mv 16 17, Step.rw 3 17 1 true,
     Step.rw 2 16 2 true, Step.rw 1 18 2 true, Step.rw 2 6 0 true, Step.rw 1 9 0 true, Step.rw 2 10 0 true,
     Step.rw 3 0 0 true, Step.rw 2 1 1 true, Step.rw 1 2 1 true, Step.rw 1 1 0 true, Step.mv 2 4, Step.rw 3 4 0 true,
     Step.rw 12 18 0 false, Step.mv 27 61, Step.mv 26 60, Step.mv 25 59, Step.mv 24 58, Step.mv 23 57, Step.mv 22 56,
     Step.mv 21 55, Step.rw 8 18 0 false, Step.mv 22 55, Step.rw 0 55 0 false, Step.rw 1 21 0 false,
     Step.rw 2 18 0 false, Step.rw 1 30 2 false, Step.mv 28 25, Step.mv 29 26, Step.mv 30 27, Step.mv 31 28,
     Step.rw 2 25 2 false, Step.rw 7 12 0 true, Step.mv 14 13, Step.rw 3 11 0 false, Step.mv 11 7,
     Step.rw 1 6 0 false, Step.rw 5 9 1 false, Step.rw 5 8 1 false, Step.rw 5 7 1 false, Step.rw 2 8 1 false,
     Step.rw 7 9 0 false, Step.rw 6 7 1 false, Step.mv 20 45, Step.mv 19 44, Step.mv 18 43, Step.mv 17 42, Step.mv 16 41,
     Step.mv 15 40, Step.mv 14 39, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.mv 15 14,
     Step.rw 17 6 1 false, Step.mv 22 51, Step.mv 21 50, Step.mv 20 49, Step.mv 19 48, Step.mv 18 47, Step.mv 17 46,
     Step.mv 16 45, Step.rw 0 51 0 false, Step.mv 11 10, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.mv 16 14,
     Step.mv 17 15, Step.mv 18 16, Step.mv 19 17, Step.mv 20 18, Step.rw 10 9 1 false, Step.mv 14 44, Step.mv 13 43,
     Step.rw 0 43 0 false, Step.rw 1 12 1 false, Step.rw 4 12 0 false, Step.rw 4 11 0 false,
     Step.rw 4 10 0 false, Step.mv 15 12, Step.mv 16 13, Step.mv 17 14, Step.mv 18 15, Step.rw 16 16 1 false,
     Step.mv 16 12, Step.mv 20 19, Step.mv 22 20, Step.mv 23 21, Step.mv 24 22, Step.rw 1 21 1 false,
     Step.rw 13 14 1 false, Step.mv 17 16, Step.mv 19 17, Step.mv 22 18, Step.mv 23 19, Step.mv 24 20,
     Step.rw 11 22 2 false, Step.mv 31 50, Step.mv 30 49, Step.mv 29 48, Step.mv 28 47, Step.mv 21 16, Step.mv 22 17,
     Step.rw 1 16 2 false, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24,
     Step.rw 5 25 1 false, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23,
     Step.rw 5 24 1 false, Step.mv 19 16, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20,
     Step.rw 16 21 1 false, Step.mv 21 16, Step.mv 25 24, Step.mv 27 25, Step.mv 28 26, Step.mv 29 27, Step.mv 30 28,
     Step.mv 31 29, Step.mv 32 30, Step.mv 33 31, Step.rw 11 24 1 false, Step.mv 33 52, Step.mv 32 51, Step.mv 31 50,
     Step.mv 30 49, Step.rw 0 49 0 false, Step.rw 1 23 1 false, Step.rw 4 21 1 false, Step.mv 23 22, Step.mv 24 23,
     Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.rw 4 20 1 false, Step.mv 22 21,
     Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 28 21, Step.mv 29 22,
     Step.mv 30 23, Step.mv 31 24, Step.rw 2 21 2 false, Step.rw 13 17 1 false, Step.mv 20 19, Step.mv 22 20,
     Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26, Step.mv 31 27,
     Step.rw 2 19 1 false, Step.rw 1 27 2 false, Step.mv 13 11, Step.mv 14 12, Step.mv 17 16, Step.rw 18 13 1 false,
     Step.mv 13 11, Step.mv 16 15, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22,
     Step.rw 1 25 2 false, Step.rw 14 12 1 false, Step.rw 1 19 1 false, Step.rw 4 20 0 false,
     Step.rw 4 19 0 false, Step.rw 4 18 0 false, Step.mv 23 20, Step.mv 24 21, Step.mv 25 22, Step.mv 26 23,
     Step.rw 16 24 1 false, Step.mv 24 20, Step.mv 28 27, Step.mv 30 28, Step.mv 31 29, Step.rw 4 24 1 false,
     Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.rw 4 23 1 false, Step.mv 25 24, Step.mv 26 25,
     Step.mv 27 26, Step.mv 28 27, Step.mv 28 24, Step.mv 29 25, Step.mv 30 26, Step.mv 31 27, Step.rw 2 24 2 false,
     Step.rw 4 22 1 false, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 12 10, Step.mv 21 18,
     Step.rw 20 8 0 false, Step.mv 13 12, Step.mv 15 13, Step.mv 18 14, Step.mv 19 15, Step.mv 20 16, Step.mv 21 17,
     Step.rw 1 7 1 false, Step.rw 1 11 1 false, Step.rw 2 15 2 false, Step.mv 7 6, Step.rw 5 7 1 false,
     Step.rw 4 8 0 false, Step.rw 2 9 1 false, Step.rw 7 7 0 true, Step.mv 7 6, Step.rw 3 4 0 false,
     Step.rw 2 10 1 true, Step.mv 22 10, Step.mv 23 12, Step.mv 24 14, Step.mv 25 15, Step.rw 13 8 1 true,
     Step.rw 5 15 0 true, Step.mv 15 5, Step.rw 5 16 0 true, Step.mv 16 6, Step.rw 5 13 1 true, Step.mv 13 10,
     Step.rw 5 14 1 true, Step.mv 14 11, Step.rw 1 12 1 true, Step.rw 1 7 1 true, Step.mv 9 8, Step.mv 16 12,
     Step.mv 17 14, Step.rw 16 9 1 true, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.rw 1 7 0 true,
     Step.rw 2 8 0 true, Step.rw 0 28 0 true, Step.mv 35 11, Step.rw 9 7 0 true, Step.mv 13 10, Step.mv 14 11,
     Step.mv 15 12, Step.mv 16 13, Step.rw 15 0 0 true, Step.mv 3 2, Step.rw 4 1 0 true, Step.mv 4 3, Step.mv 9 6,
     Step.mv 10 7, Step.mv 12 8, Step.mv 12 9, Step.mv 13 10, Step.mv 14 11, Step.mv 19 16])
    (by decide +kernel)

/-- Equation 3.59 (supplement: `[ZZ 0 1 B 3 1 2 B 2 0 1]·ω^0 = [B 2 1 2 B 3 0 1 H 1 S 1 H 1 ZZ 1 2 X 0 S 1 H 2 S 2]·ω^7`). -/
theorem rule_3_59 :
    Holds 3 ([Lt.CZ 1] ++ bB 3 0 ++ bB 2 1)
      (bB 2 0 ++ bB 3 1 ++ [.H 1, .S 1, .H 1, .CZ 0] ++ bX 2 ++ [.S 1, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 5 4, Step.mv 9 8, Step.rw 4 2 0 false, Step.mv 4 3, Step.rw 15 1 0 false, Step.rw 16 12 1 false, Step.mv 16 15,
     Step.mv 18 16, Step.mv 19 17, Step.mv 20 18, Step.mv 11 6, Step.mv 12 7, Step.rw 1 6 1 false, Step.rw 1 15 1 false,
     Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.rw 5 17 1 false, Step.mv 14 13, Step.mv 15 14, Step.mv 16 15,
     Step.rw 5 16 1 false, Step.rw 13 13 1 false, Step.mv 16 15, Step.mv 18 16, Step.mv 21 17, Step.mv 22 18,
     Step.rw 2 15 1 false, Step.rw 3 0 0 true, Step.rw 1 1 1 true, Step.rw 1 1 0 true, Step.mv 2 3,
     Step.rw 3 3 0 true, Step.rw 3 4 1 true, Step.rw 2 5 2 true, Step.rw 1 6 2 true, Step.rw 1 5 1 true, Step.mv 6 8,
     Step.rw 3 8 1 true, Step.rw 3 9 0 true, Step.rw 4 16 1 false, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19,
     Step.mv 21 20, Step.rw 4 15 1 false, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19,
     Step.rw 4 14 1 false, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.rw 8 22 0 true,
     Step.mv 22 19, Step.mv 24 20, Step.rw 3 18 0 false, Step.mv 18 17, Step.rw 1 16 0 false, Step.rw 5 20 1 true,
     Step.mv 20 17, Step.mv 29 24, Step.rw 8 23 0 false, Step.rw 7 21 1 false, Step.mv 34 47, Step.mv 33 46,
     Step.mv 32 45, Step.mv 31 44, Step.mv 30 43, Step.mv 29 42, Step.mv 28 41, Step.mv 21 18, Step.mv 22 19, Step.mv 25 24,
     Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29, Step.mv 31 30, Step.mv 32 31, Step.mv 33 32,
     Step.mv 34 33, Step.mv 20 17, Step.mv 21 18, Step.mv 22 19, Step.rw 16 20 1 false, Step.mv 20 17, Step.mv 24 23,
     Step.mv 26 24, Step.mv 27 25, Step.mv 28 26, Step.mv 29 27, Step.mv 30 28, Step.mv 31 29, Step.mv 32 30, Step.mv 33 31,
     Step.mv 34 32, Step.mv 35 33, Step.mv 36 34, Step.mv 37 35, Step.rw 1 16 1 false, Step.rw 10 22 1 false,
     Step.mv 26 43, Step.rw 0 43 0 false, Step.rw 9 20 1 false, Step.mv 24 43, Step.rw 12 20 1 false, Step.mv 29 45,
     Step.mv 28 44, Step.mv 27 43, Step.mv 26 42, Step.mv 25 41, Step.mv 24 40, Step.mv 23 39, Step.rw 0 39 0 false,
     Step.rw 4 18 1 false, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24,
     Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.mv 29 19, Step.mv 30 20, Step.mv 31 21, Step.mv 32 22,
     Step.rw 2 19 2 false, Step.rw 4 17 1 false, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21,
     Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26, Step.mv 28 27, Step.rw 4 16 1 false,
     Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24,
     Step.mv 26 25, Step.mv 27 26, Step.rw 8 15 0 false, Step.rw 3 14 1 false, Step.mv 14 13, Step.mv 15 14,
     Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22,
     Step.mv 24 23, Step.rw 14 14 0 false, Step.mv 30 45, Step.mv 29 44, Step.mv 28 43, Step.mv 27 42, Step.mv 26 41,
     Step.mv 25 40, Step.mv 24 39, Step.mv 18 17, Step.mv 20 18, Step.mv 24 19, Step.mv 25 20, Step.mv 26 21, Step.mv 27 22,
     Step.mv 28 23, Step.rw 2 17 0 false, Step.rw 1 24 1 false, Step.rw 4 13 0 true, Step.rw 6 14 0 false,
     Step.mv 27 43, Step.mv 26 42, Step.mv 25 41, Step.mv 24 40, Step.mv 23 39, Step.mv 22 38, Step.mv 21 37,
     Step.rw 0 43 0 false, Step.mv 21 18, Step.mv 22 19, Step.mv 23 20, Step.rw 11 21 1 false, Step.mv 26 36,
     Step.mv 25 35, Step.rw 0 35 0 false, Step.rw 13 13 0 false, Step.mv 16 15, Step.mv 18 16, Step.mv 21 17,
     Step.mv 22 18, Step.mv 23 19, Step.mv 24 20, Step.rw 1 12 1 false, Step.rw 2 13 0 false, Step.rw 1 18 1 false,
     Step.rw 2 16 1 false, Step.mv 15 13, Step.mv 16 14, Step.rw 1 13 1 false, Step.mv 16 15, Step.mv 17 16,
     Step.mv 18 17, Step.mv 19 18, Step.rw 5 19 1 false, Step.rw 13 16 1 false, Step.mv 19 18, Step.mv 21 19,
     Step.mv 24 20, Step.mv 15 12, Step.mv 16 13, Step.rw 1 12 2 false, Step.rw 1 22 2 false, Step.rw 2 20 2 false,
     Step.mv 19 16, Step.mv 20 17, Step.rw 1 16 2 false, Step.rw 8 11 0 true, Step.mv 13 12, Step.mv 14 13,
     Step.rw 3 9 0 false, Step.mv 12 10, Step.mv 13 11, Step.rw 3 10 1 false, Step.mv 12 10, Step.rw 4 9 0 true,
     Step.mv 13 11, Step.rw 4 10 0 true, Step.rw 1 15 2 true, Step.rw 2 16 2 true, Step.rw 1 18 2 true,
     Step.rw 1 11 1 true, Step.rw 2 12 1 true, Step.rw 0 29 0 true, Step.mv 36 15, Step.rw 10 11 1 true,
     Step.mv 21 14, Step.mv 22 15, Step.mv 23 16, Step.mv 24 17, Step.rw 15 4 1 true, Step.mv 7 6, Step.rw 4 5 1 true,
     Step.mv 2 1, Step.mv 8 7, Step.mv 17 14, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17, Step.mv 20 18])
    (by decide +kernel)

/-- Equation 3.60 (supplement: `[ZZ 0 1 B 3 1 2 B 3 0 1]·ω^0 = [B 2 1 2 B 2 0 1 ZZ 1 2 H 1 S 1 H 2 S 2]·ω^0`). -/
theorem rule_3_60 :
    Holds 3 ([Lt.CZ 1] ++ bB 3 0 ++ bB 3 1)
      (bB 2 0 ++ bB 2 1 ++ [.CZ 0, .H 1, .S 1, .H 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [Step.mv 5 4, Step.mv 11 10, Step.rw 4 2 0 false, Step.mv 4 3, Step.rw 15 1 0 false, Step.mv 15 12, Step.mv 16 13,
     Step.rw 16 14 1 false, Step.mv 14 12, Step.mv 18 17, Step.mv 20 18, Step.mv 21 19, Step.mv 22 20, Step.mv 11 6,
     Step.mv 12 7, Step.rw 1 6 1 false, Step.rw 1 17 1 false, Step.rw 4 12 1 false, Step.mv 14 13, Step.mv 15 14,
     Step.mv 16 15, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.rw 5 19 1 false, Step.mv 15 14,
     Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.rw 5 18 1 false, Step.rw 13 15 1 false, Step.mv 18 17,
     Step.mv 20 18, Step.mv 23 19, Step.mv 24 20, Step.rw 2 17 1 false, Step.rw 15 11 1 false, Step.rw 1 24 2 false,
     Step.rw 2 22 2 false, Step.mv 21 16, Step.mv 22 17, Step.rw 1 16 2 false, Step.rw 2 10 0 true,
     Step.rw 3 0 0 true, Step.rw 1 1 1 true, Step.rw 1 1 0 true, Step.mv 2 3, Step.rw 3 3 0 true, Step.rw 3 4 1 true,
     Step.rw 1 5 2 true, Step.rw 1 5 1 true, Step.mv 6 7, Step.rw 3 7 1 true, Step.rw 12 22 0 false, Step.mv 31 43,
     Step.mv 30 42, Step.mv 29 41, Step.mv 28 40, Step.mv 27 39, Step.mv 26 38, Step.mv 25 37, Step.rw 9 22 0 false,
     Step.mv 26 37, Step.rw 0 37 0 false, Step.rw 8 16 0 true, Step.mv 18 17, Step.rw 3 15 0 false, Step.mv 15 14,
     Step.rw 1 13 0 false, Step.rw 5 14 1 true, Step.mv 23 18, Step.rw 8 17 0 false, Step.rw 7 15 1 false,
     Step.mv 28 43, Step.mv 27 42, Step.mv 26 41, Step.mv 25 40, Step.mv 24 39, Step.mv 23 38, Step.mv 22 37, Step.mv 19 18,
     Step.mv 20 19, Step.mv 21 20, Step.mv 22 21, Step.mv 23 22, Step.mv 24 23, Step.mv 25 24, Step.mv 26 25, Step.mv 27 26,
     Step.mv 28 27, Step.rw 16 14 1 false, Step.mv 18 17, Step.mv 20 18, Step.mv 21 19, Step.mv 22 20, Step.mv 23 21,
     Step.mv 24 22, Step.mv 25 23, Step.mv 26 24, Step.mv 27 25, Step.mv 28 26, Step.mv 29 27, Step.mv 30 28, Step.mv 31 29,
     Step.rw 1 13 1 false, Step.rw 10 16 1 false, Step.mv 20 39, Step.rw 0 39 0 false, Step.rw 9 14 1 false,
     Step.mv 18 39, Step.rw 12 14 1 false, Step.mv 23 41, Step.mv 22 40, Step.mv 21 39, Step.mv 20 38, Step.mv 19 37,
     Step.mv 18 36, Step.mv 17 35, Step.rw 0 35 0 false, Step.mv 24 14, Step.mv 25 15, Step.mv 26 16, Step.mv 27 17,
     Step.rw 2 14 2 false, Step.rw 8 12 0 false, Step.rw 3 11 1 false, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12,
     Step.mv 14 13, Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20,
     Step.mv 21 9, Step.mv 22 10, Step.rw 1 9 2 false, Step.rw 14 11 0 false, Step.mv 27 39, Step.mv 26 38,
     Step.mv 25 37, Step.mv 24 36, Step.mv 23 35, Step.mv 22 34, Step.mv 21 33, Step.mv 15 14, Step.mv 17 15, Step.mv 21 16,
     Step.mv 22 17, Step.mv 23 18, Step.mv 24 19, Step.mv 25 20, Step.rw 2 14 0 false, Step.rw 1 21 1 false,
     Step.rw 4 10 0 true, Step.rw 6 11 0 false, Step.mv 24 37, Step.mv 23 36, Step.mv 22 35, Step.mv 21 34,
     Step.mv 20 33, Step.mv 19 32, Step.mv 18 31, Step.rw 0 37 0 false, Step.mv 18 15, Step.mv 19 16, Step.mv 20 17,
     Step.rw 11 18 1 false, Step.mv 23 30, Step.mv 22 29, Step.rw 0 29 0 false, Step.rw 13 10 0 false, Step.mv 13 12,
     Step.mv 15 13, Step.mv 18 14, Step.mv 19 15, Step.mv 20 16, Step.mv 21 17, Step.rw 1 9 1 false,
     Step.rw 2 10 0 false, Step.rw 1 15 1 false, Step.rw 2 13 1 false, Step.mv 12 10, Step.mv 13 11,
     Step.rw 1 10 1 false, Step.rw 5 12 1 false, Step.rw 2 13 1 false, Step.mv 12 10, Step.rw 8 9 0 false,
     Step.rw 3 7 1 false, Step.mv 2 1, Step.mv 6 5, Step.mv 11 9, Step.mv 12 10])
    (by decide +kernel)

end QCert.SelingerClifford
