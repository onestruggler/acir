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
    Holds 3 ([.CZ 0] ++ bB 2 1)
      (bB 2 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC12 db_ok_nil)))
    (steps := [.mv 3 2, .rw 1 0 1 true, .rw 2 2 0 false, .rw 1 0 1 false, .rw 0 1 1 true, .mv 5 2,
     .rw 1 3 1 true, .mv 2 1])
    (by decide +kernel)

/-- Equation 3.42 (supplement: `[ZZ 1 2 B 3 0 1]·ω^0 = [B 3 0 1 ZZ 0 1 H 1 ZZ 1 2 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_42 :
    Holds 3 ([.CZ 0] ++ bB 3 1)
      (bB 3 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL9 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil))))))))))))))))))
    (steps := [.mv 5 4, .rw 4 2 1 false, .mv 4 3, .rw 16 1 1 false, .rw 0 15 0 true, .mv 22 15, .mv 22 16,
     .rw 11 11 2 true, .mv 22 16, .mv 22 17, .mv 22 18, .mv 22 19, .mv 22 20, .mv 22 21,
     .rw 13 11 2 true, .rw 0 19 0 true, .mv 26 17, .mv 26 18, .mv 26 19, .mv 26 20,
     .rw 12 11 2 true, .mv 22 10, .rw 9 6 1 true, .rw 0 22 0 true, .mv 29 9, .mv 29 10,
     .mv 29 11, .mv 29 12, .mv 29 13, .mv 29 14, .mv 29 15, .rw 14 6 1 true, .mv 26 10,
     .rw 9 6 1 true, .mv 25 12, .rw 10 8 1 true, .mv 3 2, .mv 4 3, .mv 15 7, .mv 16 9,
     .rw 17 4 1 true, .mv 4 2, .mv 5 3, .mv 6 4, .rw 0 21 0 true, .mv 28 19, .mv 28 20,
     .mv 28 21, .mv 28 22, .rw 12 13 2 true, .mv 5 3, .mv 6 4, .mv 13 8, .rw 0 25 0 true,
     .mv 32 12, .mv 32 13, .mv 32 14, .mv 32 15, .mv 32 16, .mv 32 17, .mv 32 18,
     .rw 7 5 1 true, .mv 3 2, .mv 4 3, .rw 5 4 1 false, .mv 10 8, .rw 4 7 1 true,
     .rw 1 8 2 true, .mv 13 11, .mv 14 13, .rw 15 9 1 true, .rw 3 5 0 true, .rw 4 6 0 true,
     .rw 4 5 0 true, .mv 9 6, .mv 10 7, .mv 11 8, .mv 21 9, .mv 21 10, .mv 21 11, .mv 21 12,
     .mv 21 13, .mv 21 14, .mv 21 15, .rw 6 2 1 true, .rw 8 4 0 true, .mv 4 3,
     .rw 3 1 1 false, .rw 3 0 0 false, .rw 2 6 2 true, .rw 1 8 2 true, .rw 0 13 0 true,
     .mv 20 9, .mv 20 10, .mv 20 11, .mv 20 12, .mv 20 13, .mv 20 14, .rw 13 4 2 true,
     .rw 2 2 1 true, .mv 8 2, .mv 9 4, .mv 10 6, .mv 11 7, .rw 15 0 1 true, .mv 16 12,
     .rw 9 8 2 true, .mv 15 14, .rw 10 10 2 true, .rw 0 15 0 true, .mv 22 12, .mv 22 13,
     .rw 11 8 2 true, .mv 8 5, .mv 9 6, .mv 10 7, .rw 0 23 0 true, .mv 30 8, .mv 30 9,
     .mv 30 10, .mv 30 11, .mv 30 12, .mv 30 13, .mv 30 14, .rw 6 1 1 true, .rw 4 0 1 false,
     .mv 19 12, .mv 19 13, .mv 19 14, .mv 19 15, .mv 19 16, .mv 19 17, .rw 13 7 2 true,
     .rw 0 16 0 true, .mv 23 13, .mv 23 14, .mv 23 15, .mv 23 16, .rw 12 7 2 true,
     .rw 1 4 1 true, .rw 2 5 1 true, .rw 1 7 1 true, .rw 1 1 1 true, .mv 3 2, .mv 4 3,
     .mv 17 7, .mv 18 9, .rw 17 4 1 true, .mv 4 2, .mv 5 3, .mv 6 4, .mv 25 19, .mv 25 20,
     .rw 11 15 2 true, .mv 25 12, .mv 25 13, .rw 11 8 1 true, .mv 5 3, .mv 6 4, .mv 17 8,
     .rw 0 26 0 true, .mv 33 12, .mv 33 13, .mv 33 14, .mv 33 15, .mv 33 16, .mv 33 17,
     .mv 33 18, .rw 7 5 1 true, .mv 3 2, .mv 4 3, .rw 5 4 1 false, .rw 2 8 1 true,
     .rw 1 7 2 true, .mv 20 10, .mv 21 12, .mv 22 14, .mv 23 15, .rw 15 8 1 true, .mv 24 16,
     .rw 9 12 1 true, .mv 23 18, .rw 10 14 1 true, .mv 7 6, .mv 8 7, .mv 9 8, .mv 10 9,
     .mv 20 13, .mv 21 15, .rw 17 10 1 true, .mv 10 6, .mv 11 7, .mv 12 8, .rw 5 13 1 true,
     .mv 13 9, .rw 16 0 1 true, .mv 3 2, .rw 4 1 1 true, .mv 4 3])
    (by decide +kernel)

/-- Equation 3.43 (supplement: `[ZZ 1 2 B 4 0 1]·ω^0 = [B 4 0 1 ZZ 0 1 H 1 ZZ 1 2 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_43 :
    Holds 3 ([.CZ 0] ++ bB 4 1)
      (bB 4 1 ++ [.CZ 1, .H 1, .CZ 0, .H 1, .CZ 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC12 db_ok_nil)))
    (steps := [.mv 4 3, .rw 1 0 0 true, .mv 3 2, .rw 2 3 0 false, .rw 1 0 0 false, .rw 0 2 1 true, .mv 6 3,
     .rw 1 4 1 true, .mv 3 2])
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
    (steps := [.rw 0 3 0 false, .rw 1 1 0 false, .rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.46 (supplement: `[S 0 C 1 0]·ω^0 = [C 1 0 S 0]·ω^0`). -/
theorem rule_3_46 :
    Holds 1 ([.S 0] ++ bC 1 0)
      (bC 1 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.47 (supplement: `[S 0 C 2 0]·ω^0 = [C 2 0 S 0 S 0 S 0]·ω^2`). -/
theorem rule_3_47 :
    Holds 1 ([.S 0] ++ bC 2 0)
      (bC 2 0 ++ [.S 0, .S 0, .S 0, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hL9 db_ok_nil))
    (steps := [.rw 0 5 0 true, .mv 12 5, .mv 12 6, .mv 12 7, .mv 12 8, .mv 12 9, .mv 12 10, .rw 1 0 0 true])
    (by decide +kernel)

/-- Equation 3.48 (supplement: `[ZZ 0 1 C 1 0]·ω^0 = [C 1 0 ZZ 0 1]·ω^0`). -/
theorem rule_3_48 :
    Holds 2 ([.CZ 0] ++ bC 1 1)
      (bC 1 1 ++ [.CZ 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.49 (supplement: `[ZZ 0 1 C 2 0]·ω^0 = [C 2 0 ZZ 0 1 S 1 S 1]·ω^0`). -/
theorem rule_3_49 :
    Holds 2 ([.CZ 0] ++ bC 2 1)
      (bC 2 1 ++ [.CZ 0, .S 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL14 db_ok_nil)))
    (steps := [.rw 1 1 0 true, .rw 0 0 1 true, .mv 7 3, .mv 8 5, .mv 9 7, .mv 10 8, .rw 2 1 0 true])
    (by decide +kernel)

/-- Equation 3.50 (supplement: `[ZZ 0 1 B 1 1 2 B 1 0 1]·ω^0 = [B 1 1 2 B 1 0 1 H 1 H 2 ZZ 1 2 H 1 H 2]·ω^0`). -/
theorem rule_3_50 :
    Holds 3 ([.CZ 1] ++ bB 1 0 ++ bB 1 1)
      (bB 1 0 ++ bB 1 1 ++ [.H 1, .H 0, .CZ 0, .H 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 (db_ok_cons hM18 (db_ok_cons hM20 db_ok_nil))))))))))))))))))
    (steps := [.mv 1 0, .mv 7 6, .mv 15 14, .mv 1 0, .mv 4 3, .mv 7 6, .rw 16 1 0 false, .mv 3 2, .mv 6 5,
     .rw 1 8 1 false, .rw 1 8 2 true, .rw 3 9 1 true, .rw 1 10 2 true, .rw 1 10 1 true,
     .mv 12 11, .rw 3 12 1 true, .rw 1 13 1 true, .rw 1 8 0 true, .mv 10 4, .mv 11 10,
     .mv 12 11, .mv 13 12, .mv 14 13, .mv 15 14, .rw 17 3 0 true, .mv 6 5, .mv 7 6, .mv 8 7,
     .mv 9 8, .mv 10 9, .rw 2 16 1 true, .rw 1 17 1 true, .rw 12 10 1 true, .rw 2 23 2 true,
     .mv 23 16, .rw 4 15 1 true, .mv 24 17, .rw 4 16 1 true, .mv 25 18, .rw 4 17 1 true,
     .rw 2 26 2 true, .rw 1 22 1 true, .mv 14 13, .mv 15 14, .mv 16 15, .mv 17 16, .mv 28 20,
     .mv 29 22, .rw 13 17 1 true, .mv 17 13, .mv 18 14, .mv 19 15, .rw 0 41 0 true,
     .mv 48 20, .rw 9 16 2 true, .mv 16 14, .mv 17 15, .mv 18 16, .mv 47 17, .mv 47 18,
     .mv 47 19, .mv 47 20, .mv 47 21, .mv 47 22, .mv 47 23, .rw 5 10 1 true, .rw 1 25 2 true,
     .rw 0 39 0 true, .mv 46 26, .rw 8 22 2 true, .mv 45 25, .mv 45 26, .mv 45 27, .mv 45 28,
     .mv 45 29, .mv 45 30, .mv 45 31, .rw 11 22 2 true, .rw 2 18 1 true, .rw 1 20 1 true,
     .mv 15 13, .mv 28 17, .mv 29 18, .mv 30 19, .mv 31 20, .mv 32 21, .rw 15 12 1 true,
     .mv 12 11, .mv 15 14, .mv 16 15, .rw 1 21 1 true, .rw 0 43 0 true, .mv 50 22, .mv 50 23,
     .rw 10 18 1 true, .mv 16 14, .mv 29 19, .mv 30 21, .rw 0 51 0 true, .mv 58 25,
     .mv 58 26, .mv 58 27, .mv 58 28, .mv 58 29, .mv 58 30, .mv 58 31, .rw 14 15 1 true,
     .mv 15 14, .mv 16 15, .mv 17 16, .mv 17 15, .mv 25 19, .mv 45 23, .mv 45 24, .mv 45 25,
     .mv 45 26, .mv 45 27, .mv 45 28, .mv 45 29, .rw 6 16 1 true, .rw 7 18 0 true, .mv 20 19,
     .mv 22 21, .mv 25 24, .rw 16 20 1 true, .mv 23 22, .mv 26 25, .rw 1 2 0 true,
     .rw 3 4 0 true, .mv 7 6, .rw 7 5 0 false, .rw 1 2 0 false, .rw 3 1 0 false,
     .rw 3 0 1 false, .rw 3 25 1 false, .mv 25 24, .rw 1 23 1 false, .rw 1 23 2 false,
     .rw 3 22 1 false, .mv 22 21, .rw 1 20 1 false, .rw 1 20 2 false, .rw 3 19 1 false,
     .rw 1 8 1 true, .mv 2 1, .mv 5 4, .mv 8 7, .rw 16 0 0 true, .mv 3 2, .mv 6 5, .mv 6 5,
     .mv 9 8, .mv 10 9, .mv 11 10, .mv 12 11, .mv 13 12, .mv 15 13, .mv 15 14, .mv 16 15,
     .mv 17 16, .mv 20 19])
    (by decide +kernel)

/-- Equation 3.51 (supplement: `[ZZ 0 1 B 1 1 2 B 2 0 1]·ω^0 = [B 4 1 2 B 2 0 1 H 2 ZZ 1 2 H 2]·ω^0`). -/
theorem rule_3_51 :
    Holds 3 ([.CZ 1] ++ bB 1 0 ++ bB 2 1)
      (bB 4 0 ++ bB 2 1 ++ [.H 0, .CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil))))))))))))))))))
    (steps := [.mv 1 0, .mv 7 6, .mv 11 10, .mv 1 0, .mv 4 3, .mv 7 6, .rw 17 1 0 false, .mv 3 2, .mv 6 5,
     .rw 1 8 0 true, .mv 9 14, .rw 3 14 0 true, .rw 3 15 1 true, .rw 1 15 0 true,
     .rw 1 0 1 true, .rw 3 1 0 true, .rw 1 2 1 true, .rw 7 6 0 true, .mv 8 7,
     .rw 6 4 0 false, .mv 17 37, .mv 16 36, .mv 15 35, .mv 14 34, .mv 13 33, .mv 12 32,
     .mv 11 31, .mv 11 8, .rw 12 3 0 false, .mv 19 43, .mv 18 42, .mv 17 41, .mv 16 40,
     .mv 15 39, .mv 14 38, .mv 13 37, .rw 0 43 0 false, .mv 7 6, .mv 9 7, .mv 13 8, .mv 14 9,
     .rw 9 10 1 false, .mv 15 36, .mv 14 35, .rw 0 35 0 false, .rw 1 13 1 false, .mv 29 27,
     .rw 7 26 0 false, .rw 3 25 1 false, .mv 25 24, .mv 26 25, .mv 27 26, .rw 5 13 1 false,
     .rw 13 14 0 false, .rw 1 21 0 false, .rw 5 12 1 false, .rw 13 13 0 false,
     .rw 1 20 0 false, .rw 5 11 1 false, .rw 13 12 0 false, .rw 1 19 0 false, .mv 10 7,
     .mv 11 8, .mv 12 9, .rw 15 10 0 false, .mv 10 7, .mv 14 13, .mv 16 14, .mv 17 15,
     .mv 18 16, .rw 1 15 0 false, .rw 11 15 0 false, .mv 18 17, .mv 20 18, .mv 23 19,
     .mv 24 20, .mv 25 21, .mv 26 22, .rw 1 26 1 false, .mv 15 14, .rw 5 15 0 false,
     .rw 10 16 0 false, .mv 25 37, .mv 24 36, .mv 23 35, .mv 22 34, .mv 21 33, .mv 20 32,
     .mv 19 31, .mv 14 13, .rw 5 14 0 false, .rw 8 15 0 false, .mv 19 31, .rw 0 31 0 false,
     .mv 8 6, .mv 9 7, .mv 10 8, .mv 13 12, .rw 16 9 0 false, .mv 9 6, .mv 12 11, .mv 17 14,
     .mv 18 15, .mv 19 16, .mv 20 17, .rw 1 20 1 false, .rw 5 21 1 false, .rw 5 20 1 false,
     .rw 11 21 0 false, .mv 24 23, .mv 26 24, .mv 29 25, .mv 30 26, .rw 5 19 1 false,
     .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20, .rw 5 21 0 false, .mv 17 16, .mv 18 17,
     .mv 19 18, .mv 20 19, .rw 5 20 0 false, .rw 2 21 0 false, .mv 16 15, .mv 17 16,
     .mv 18 17, .mv 19 18, .rw 5 19 0 false, .mv 7 6, .mv 12 11, .mv 15 14, .rw 14 5 0 false,
     .mv 6 2, .mv 9 8, .mv 11 9, .mv 13 10, .mv 14 11, .mv 15 12, .mv 16 13, .mv 17 14,
     .rw 1 5 1 false, .rw 2 7 0 false, .rw 1 6 0 false, .rw 1 9 1 false, .rw 4 4 0 false,
     .mv 6 5, .rw 5 6 1 false, .rw 2 7 1 false, .mv 3 2, .mv 6 5, .mv 8 6, .mv 8 7, .mv 9 8])
    (by decide +kernel)

/-- Equation 3.52 (supplement: `[ZZ 0 1 B 1 1 2 B 3 0 1]·ω^0 = [B 4 1 2 B 3 0 1 H 2 H 1 S 1 H 1 ZZ 2 1 S 1 H 1 S 1 H 2]·ω^7`). -/
theorem rule_3_52 :
    Holds 3 ([.CZ 1] ++ bB 1 0 ++ bB 3 1)
      (bB 4 0 ++ bB 3 1 ++ [.H 0, .H 1, .S 1, .H 1, .CZ 0, .S 1, .H 1, .S 1, .H 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil))))))))))))))))))))
    (steps := [.mv 1 0, .mv 7 6, .mv 13 12, .rw 4 10 1 false, .mv 12 11, .rw 15 9 1 false, .mv 1 0, .mv 4 3,
     .mv 7 6, .rw 19 1 0 false, .mv 3 2, .mv 6 5, .rw 1 8 0 true, .mv 9 15, .rw 3 15 0 true,
     .rw 3 16 1 true, .rw 1 16 2 true, .rw 2 17 2 true, .rw 1 19 2 true, .rw 2 15 1 true,
     .rw 2 15 1 true, .rw 1 18 1 true, .rw 2 19 1 true, .rw 1 0 1 true, .rw 3 1 0 true,
     .rw 1 2 1 true, .rw 1 2 0 true, .rw 11 23 1 false, .mv 32 61, .mv 31 60, .mv 30 59,
     .mv 29 58, .mv 28 57, .mv 27 56, .mv 26 55, .rw 8 23 1 false, .mv 27 55,
     .rw 0 55 0 false, .rw 1 26 1 false, .rw 2 23 1 false, .rw 2 23 1 false,
     .rw 1 27 2 false, .rw 2 25 2 false, .mv 24 23, .mv 25 24, .rw 1 23 2 false,
     .rw 7 8 0 true, .mv 10 9, .rw 6 6 0 false, .mv 19 47, .mv 18 46, .mv 17 45, .mv 16 44,
     .mv 15 43, .mv 14 42, .mv 13 41, .mv 13 10, .rw 13 5 0 false, .mv 21 53, .mv 20 52,
     .mv 19 51, .mv 18 50, .mv 17 49, .mv 16 48, .mv 15 47, .rw 0 53 0 false, .mv 9 8,
     .mv 11 9, .mv 15 10, .mv 16 11, .rw 10 12 1 false, .mv 17 46, .mv 16 45,
     .rw 0 45 0 false, .rw 1 15 1 false, .rw 7 29 0 false, .rw 3 28 1 false, .mv 28 26,
     .rw 5 15 1 false, .rw 14 16 0 false, .rw 1 23 0 false, .rw 5 14 1 false,
     .rw 14 15 0 false, .rw 1 22 0 false, .rw 5 13 1 false, .rw 14 14 0 false,
     .rw 1 21 0 false, .mv 12 9, .mv 13 10, .mv 14 11, .rw 17 12 0 false, .mv 12 9,
     .mv 16 15, .mv 18 16, .mv 19 17, .mv 20 18, .rw 1 17 0 false, .rw 12 17 0 false,
     .mv 20 19, .mv 22 20, .mv 25 21, .mv 26 22, .mv 27 23, .mv 28 24, .rw 1 28 1 false,
     .mv 17 16, .rw 5 17 0 false, .rw 11 18 0 false, .mv 27 47, .mv 26 46, .mv 25 45,
     .mv 24 44, .mv 23 43, .mv 22 42, .mv 21 41, .mv 16 15, .rw 5 16 0 false,
     .rw 9 17 0 false, .mv 21 41, .rw 0 41 0 false, .mv 10 8, .mv 11 9, .mv 12 10, .mv 15 14,
     .rw 18 11 0 false, .mv 11 8, .mv 14 13, .mv 19 16, .mv 20 17, .mv 21 18, .mv 22 19,
     .rw 1 22 1 false, .rw 5 23 1 false, .rw 5 22 1 false, .rw 12 23 0 false, .mv 26 25,
     .mv 28 26, .rw 5 21 1 false, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22,
     .rw 5 23 0 false, .mv 19 18, .mv 20 19, .mv 21 20, .mv 22 21, .rw 5 22 0 false,
     .rw 2 23 0 false, .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20, .rw 5 21 0 false, .mv 9 8,
     .mv 14 13, .mv 17 16, .rw 16 7 0 false, .mv 8 4, .mv 11 10, .mv 13 11, .mv 15 12,
     .mv 16 13, .mv 17 14, .rw 1 2 0 false, .rw 1 5 1 false, .rw 2 7 0 false,
     .rw 1 9 1 false, .rw 4 4 0 false, .mv 6 5, .rw 5 6 1 false, .rw 2 7 1 false, .mv 13 12,
     .rw 4 11 0 true, .mv 14 13, .rw 4 12 0 true, .rw 1 13 1 true, .rw 2 14 1 true,
     .rw 0 28 0 true, .mv 35 17, .rw 9 13 1 true, .mv 24 16, .mv 25 17, .mv 26 18, .mv 27 19,
     .rw 15 6 1 true, .mv 9 8, .rw 4 7 1 true, .mv 3 2, .mv 6 5, .mv 7 6, .mv 8 7, .mv 10 8,
     .mv 10 9, .mv 11 10, .mv 17 16, .mv 18 17, .mv 19 18])
    (by decide +kernel)

/-- Equation 3.53 (supplement: `[ZZ 0 1 B 1 1 2 B 4 0 1]·ω^0 = [B 1 1 2 B 4 0 1 H 1 H 2 ZZ 1 2 H 1 H 2]·ω^0`). -/
theorem rule_3_53 :
    Holds 3 ([.CZ 1] ++ bB 1 0 ++ bB 4 1)
      (bB 1 0 ++ bB 4 1 ++ [.H 1, .H 0, .CZ 0, .H 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hL18 (db_ok_cons hL20 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil)))))))))))))))))))
    (steps := [.mv 1 0, .mv 7 6, .mv 12 11, .mv 1 0, .mv 4 3, .mv 7 6, .rw 18 1 0 false, .mv 3 2, .mv 6 5,
     .rw 1 0 2 true, .rw 3 0 0 true, .mv 1 2, .rw 1 1 1 true, .mv 2 3, .rw 1 1 0 true,
     .mv 2 4, .rw 3 3 0 true, .mv 4 5, .rw 1 4 1 true, .mv 5 6, .rw 1 4 0 true, .mv 5 7,
     .rw 3 6 0 true, .mv 7 8, .rw 1 7 1 true, .mv 8 9, .rw 3 9 1 true, .rw 1 10 2 true,
     .rw 1 10 1 true, .mv 11 12, .rw 3 12 1 true, .rw 1 13 1 true, .rw 1 7 0 true, .mv 8 15,
     .rw 3 15 0 true, .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22,
     .mv 26 25, .mv 29 28, .rw 18 23 0 false, .mv 25 24, .mv 28 27, .rw 15 22 0 false,
     .mv 30 29, .mv 31 30, .mv 32 31, .mv 35 34, .mv 38 37, .rw 18 32 0 false, .mv 34 33,
     .mv 37 36, .rw 1 39 1 false, .rw 7 31 0 true, .mv 31 30, .mv 33 31, .rw 5 28 0 false,
     .mv 41 54, .mv 40 53, .mv 39 52, .mv 38 51, .mv 37 50, .mv 36 49, .mv 35 48, .mv 35 32,
     .rw 13 27 0 false, .mv 43 60, .mv 42 59, .mv 41 58, .mv 40 57, .mv 39 56, .mv 38 55,
     .mv 37 54, .rw 0 60 0 false, .mv 31 30, .mv 33 31, .mv 37 32, .mv 38 33,
     .rw 10 34 1 false, .mv 39 53, .mv 38 52, .rw 0 52 0 false, .rw 1 37 1 false,
     .rw 14 24 0 false, .mv 38 34, .mv 39 35, .mv 40 36, .mv 41 37, .rw 11 29 0 false,
     .mv 38 60, .mv 37 59, .mv 36 58, .mv 35 57, .mv 34 56, .mv 33 55, .mv 32 54,
     .rw 8 29 0 false, .mv 33 54, .rw 0 54 0 false, .rw 1 32 0 false, .rw 1 35 1 false,
     .rw 2 33 1 false, .rw 6 22 0 false, .mv 35 56, .mv 34 55, .mv 33 54, .mv 32 53,
     .mv 31 52, .mv 30 51, .mv 29 50, .mv 22 17, .mv 23 18, .mv 26 25, .mv 27 26, .mv 28 27,
     .mv 29 28, .rw 9 25 0 false, .mv 29 50, .rw 0 50 0 false, .mv 29 28, .mv 30 29,
     .mv 31 30, .rw 4 31 0 false, .rw 2 32 0 false, .mv 28 27, .mv 29 28, .mv 30 29,
     .rw 4 30 0 false, .mv 27 26, .mv 28 27, .mv 29 28, .rw 4 29 0 false, .rw 12 26 0 false,
     .mv 29 28, .mv 31 29, .mv 34 30, .mv 35 31, .rw 2 28 0 false, .rw 1 31 1 false,
     .mv 19 17, .mv 20 18, .mv 21 19, .mv 22 20, .mv 23 21, .mv 26 25, .rw 17 22 0 false,
     .mv 22 17, .mv 25 24, .rw 1 29 1 false, .rw 2 28 1 false, .mv 18 17, .mv 21 20,
     .mv 28 23, .mv 26 25, .rw 16 16 0 false, .mv 17 16, .mv 20 19, .mv 23 22, .mv 25 23,
     .mv 25 24, .mv 26 25, .mv 27 26, .mv 28 27, .mv 29 28, .mv 30 29, .mv 31 30, .mv 32 31,
     .rw 1 26 1 false, .mv 30 22, .mv 31 23, .rw 1 22 2 false, .rw 3 25 0 false, .mv 25 24,
     .rw 1 23 0 false, .rw 1 23 1 false, .rw 3 22 0 false, .rw 3 21 1 false, .mv 21 20,
     .rw 1 19 1 false, .rw 1 19 2 false, .rw 3 18 1 false, .mv 2 1, .mv 5 4, .mv 8 7,
     .rw 18 0 0 true, .mv 3 2, .mv 6 5, .mv 6 5, .mv 9 8, .mv 10 9, .mv 12 10, .mv 12 11,
     .mv 13 12, .mv 14 13, .mv 17 16])
    (by decide +kernel)

/-- Equation 3.54 (supplement: `[ZZ 0 1 B 2 1 2 B 1 0 1]·ω^0 = [B 2 1 2 B 4 0 1 H 1 ZZ 1 2 H 1]·ω^0`). -/
theorem rule_3_54 :
    Holds 3 ([.CZ 1] ++ bB 2 0 ++ bB 1 1)
      (bB 2 0 ++ bB 4 1 ++ [.H 1, .CZ 0, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [.mv 3 2, .mv 11 10, .mv 8 7, .mv 11 10, .rw 15 5 1 false, .mv 7 6, .mv 10 9, .rw 1 12 1 true,
     .mv 13 14, .rw 3 13 0 true, .mv 14 15, .rw 1 14 1 true, .mv 15 16, .rw 3 16 1 true,
     .rw 3 0 0 true, .rw 1 1 1 true, .rw 1 1 0 true, .mv 2 3, .rw 3 3 0 true, .rw 7 8 0 true,
     .mv 10 9, .rw 3 7 0 false, .mv 7 6, .rw 1 5 0 false, .rw 7 8 0 false, .rw 6 6 1 false,
     .mv 19 35, .mv 18 34, .mv 17 33, .mv 16 32, .mv 15 31, .mv 14 30, .mv 13 29, .mv 10 9,
     .mv 11 10, .mv 12 11, .mv 13 12, .mv 14 13, .rw 13 5 1 false, .mv 21 41, .mv 20 40,
     .mv 19 39, .mv 18 38, .mv 17 37, .mv 16 36, .mv 15 35, .rw 0 41 0 false, .mv 10 9,
     .mv 12 10, .mv 13 11, .mv 14 12, .mv 15 13, .mv 16 14, .mv 17 15, .mv 18 16, .mv 19 17,
     .rw 8 8 1 false, .mv 13 34, .mv 12 33, .rw 0 33 0 false, .rw 1 11 1 false,
     .rw 4 11 0 false, .rw 4 10 0 false, .rw 4 9 0 false, .mv 14 11, .mv 15 12, .mv 16 13,
     .mv 17 14, .rw 12 15 1 false, .mv 15 11, .mv 19 18, .mv 21 19, .mv 22 20, .mv 23 21,
     .rw 1 20 1 false, .rw 10 13 1 false, .mv 16 15, .mv 18 16, .mv 21 17, .mv 22 18,
     .mv 23 19, .rw 9 21 2 false, .mv 30 40, .mv 29 39, .mv 28 38, .mv 27 37, .mv 20 15,
     .mv 21 16, .rw 1 15 2 false, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23,
     .rw 5 24 1 false, .mv 19 18, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22,
     .rw 5 23 1 false, .mv 18 15, .mv 19 16, .mv 20 17, .mv 21 18, .mv 22 19,
     .rw 12 20 1 false, .mv 20 15, .mv 24 23, .mv 26 24, .mv 27 25, .mv 28 26, .mv 29 27,
     .mv 30 28, .mv 31 29, .mv 32 30, .rw 9 23 1 false, .mv 32 42, .mv 31 41, .mv 30 40,
     .mv 29 39, .rw 0 39 0 false, .rw 1 22 1 false, .rw 4 20 1 false, .mv 22 21, .mv 23 22,
     .mv 24 23, .mv 25 24, .mv 26 25, .mv 27 26, .mv 28 27, .rw 4 19 1 false, .mv 21 20,
     .mv 22 21, .mv 23 22, .mv 24 23, .mv 25 24, .mv 26 25, .mv 27 26, .mv 27 20, .mv 28 21,
     .mv 29 22, .mv 30 23, .rw 2 20 2 false, .rw 10 16 1 false, .mv 19 18, .mv 21 19,
     .mv 24 20, .mv 25 21, .mv 26 22, .mv 27 23, .mv 28 24, .mv 29 25, .mv 30 26,
     .rw 2 18 1 false, .rw 1 26 2 false, .mv 12 10, .mv 13 11, .mv 16 15, .rw 14 12 1 false,
     .mv 12 10, .mv 15 14, .mv 20 17, .mv 21 18, .mv 22 19, .mv 23 20, .mv 24 21,
     .rw 1 24 2 false, .rw 11 11 1 false, .rw 1 18 1 false, .rw 4 19 0 false,
     .rw 4 18 0 false, .rw 4 17 0 false, .mv 22 19, .mv 23 20, .mv 24 21, .mv 25 22,
     .rw 12 23 1 false, .mv 23 19, .mv 27 26, .mv 29 27, .mv 30 28, .rw 4 23 1 false,
     .mv 25 24, .mv 26 25, .mv 27 26, .mv 28 27, .rw 4 22 1 false, .mv 24 23, .mv 25 24,
     .mv 26 25, .mv 27 26, .mv 27 23, .mv 28 24, .mv 29 25, .mv 30 26, .rw 2 23 2 false,
     .rw 4 21 1 false, .mv 23 22, .mv 24 23, .mv 25 24, .mv 26 25, .mv 11 9, .mv 20 17,
     .rw 16 7 0 false, .mv 12 11, .mv 14 12, .mv 17 13, .mv 18 14, .mv 19 15, .mv 20 16,
     .rw 1 6 1 false, .rw 1 10 1 false, .rw 2 14 2 false, .mv 6 5, .rw 5 6 1 false,
     .rw 4 7 0 false, .rw 2 8 1 false, .rw 7 6 0 true, .mv 6 5, .rw 3 3 0 false, .mv 2 1,
     .mv 7 6])
    (by decide +kernel)

/-- Equation 3.55 (supplement: `[ZZ 0 1 B 2 1 2 B 2 0 1]·ω^0 = [B 3 1 2 B 3 0 1 H 1 S 1 H 1 H 2 S 2 H 2 ZZ 1 2 S 1 S 2]·ω^6`). -/
theorem rule_3_55 :
    Holds 3 ([.CZ 1] ++ bB 2 0 ++ bB 2 1)
      (bB 3 0 ++ bB 3 1 ++ [.H 1, .S 1, .H 1, .H 0, .S 0, .H 0, .CZ 0, .S 1, .S 0, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [.mv 3 2, .mv 7 6, .rw 3 7 0 true, .mv 9 8, .rw 8 9 0 false, .rw 2 11 1 true, .rw 4 10 0 true,
     .rw 2 12 0 true, .rw 5 11 0 true, .mv 11 8, .rw 5 10 1 true, .mv 10 9, .rw 1 9 1 true,
     .rw 2 10 1 true, .rw 1 12 1 true, .rw 2 8 0 true, .mv 13 8, .mv 14 10, .mv 15 12,
     .mv 16 13, .rw 13 6 0 true, .rw 0 27 0 true, .mv 34 17, .mv 34 18, .rw 11 13 1 true,
     .mv 13 11, .mv 14 12, .mv 15 13, .rw 0 35 0 true, .mv 42 14, .mv 42 15, .mv 42 16,
     .mv 42 17, .mv 42 18, .mv 42 19, .mv 42 20, .rw 6 7 0 true, .rw 4 6 0 false,
     .rw 1 16 1 true, .mv 12 10, .mv 13 12, .mv 33 17, .mv 33 18, .mv 33 19, .mv 33 20,
     .mv 33 21, .mv 33 22, .mv 33 23, .rw 14 7 0 true, .rw 3 5 1 true, .rw 8 7 0 true,
     .rw 2 14 2 true, .rw 0 27 0 true, .mv 34 12, .mv 34 13, .mv 34 14, .mv 34 15, .mv 34 16,
     .mv 34 17, .mv 34 18, .rw 12 9 1 true, .mv 31 13, .rw 9 9 1 true, .rw 0 31 0 true,
     .mv 38 15, .rw 10 11 1 true, .rw 1 8 1 true, .mv 20 12, .mv 21 14, .rw 16 9 1 true,
     .mv 18 13, .mv 35 17, .mv 35 18, .mv 35 19, .mv 35 20, .mv 35 21, .mv 35 22, .mv 35 23,
     .rw 7 10 1 true, .rw 8 12 0 true, .rw 5 9 1 false, .rw 1 8 0 true, .mv 10 9,
     .rw 3 10 0 true, .mv 13 12, .rw 8 11 0 false, .rw 3 5 1 false, .rw 3 4 0 false, .mv 4 3,
     .rw 1 2 0 false, .rw 1 2 1 false, .rw 3 1 0 false, .rw 3 0 1 false, .mv 14 11,
     .rw 4 10 0 true, .mv 15 12, .rw 4 11 0 true, .rw 1 17 2 true, .rw 2 18 2 true,
     .rw 1 20 2 true, .rw 1 12 1 true, .rw 2 13 1 true, .rw 0 31 0 true, .mv 38 16,
     .rw 10 12 1 true, .mv 23 15, .mv 24 16, .mv 25 17, .mv 26 18, .rw 15 5 1 true,
     .mv 29 14, .mv 29 15, .mv 29 16, .mv 29 17, .mv 29 18, .mv 29 19, .mv 29 20,
     .rw 12 11 1 true, .mv 23 11, .mv 24 13, .mv 25 15, .mv 26 16, .rw 13 9 1 true,
     .rw 5 18 0 true, .mv 18 5, .rw 5 19 0 true, .mv 19 6, .rw 5 14 1 true, .mv 14 10,
     .rw 0 23 0 true, .mv 30 20, .rw 10 16 1 true, .rw 5 15 1 true, .mv 15 11, .mv 12 9,
     .rw 4 8 1 true, .rw 1 13 1 true, .rw 1 7 1 true, .mv 9 8, .mv 10 9, .mv 17 13,
     .mv 18 15, .rw 16 10 1 true, .mv 10 8, .mv 11 9, .mv 12 10, .rw 1 7 0 true,
     .rw 2 8 0 true, .mv 35 11, .rw 10 7 0 true, .mv 13 10, .mv 14 11, .mv 15 12, .mv 16 13,
     .rw 15 0 0 true, .mv 3 2, .rw 4 1 0 true, .mv 4 3, .mv 9 6, .mv 10 7, .mv 11 8,
     .mv 13 9, .mv 13 10, .mv 14 11, .mv 15 12, .mv 16 13, .mv 17 14, .mv 20 19])
    (by decide +kernel)

/-- Equation 3.56 (supplement: `[ZZ 0 1 B 2 1 2 B 3 0 1]·ω^0 = [B 3 1 2 B 2 0 1 H 2 S 2 H 2 ZZ 1 2 X 0 H 1 S 1 S 2]·ω^7`). -/
theorem rule_3_56 :
    Holds 3 ([.CZ 1] ++ bB 2 0 ++ bB 3 1)
      (bB 3 0 ++ bB 2 1 ++ [.H 0, .S 0, .H 0, .CZ 0] ++ bX 2 ++ [.H 1, .S 1, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [.mv 3 2, .mv 9 8, .rw 4 6 1 false, .mv 8 7, .rw 15 5 1 false, .rw 3 7 0 true, .mv 9 8,
     .mv 10 9, .rw 8 10 0 false, .rw 4 11 0 true, .rw 4 12 0 true, .rw 4 13 0 true,
     .rw 2 18 2 true, .rw 1 20 2 true, .mv 17 11, .mv 18 13, .mv 19 15, .mv 20 16,
     .rw 13 9 1 true, .rw 2 15 0 true, .rw 5 14 0 true, .mv 14 8, .rw 5 13 1 true, .mv 13 9,
     .rw 1 9 1 true, .rw 2 10 1 true, .rw 1 12 1 true, .rw 2 8 0 true, .mv 13 8, .mv 14 10,
     .mv 15 12, .mv 16 13, .rw 13 6 0 true, .rw 0 35 0 true, .mv 42 17, .mv 42 18,
     .rw 11 13 1 true, .mv 13 11, .mv 14 12, .mv 15 13, .rw 0 43 0 true, .mv 50 14,
     .mv 50 15, .mv 50 16, .mv 50 17, .mv 50 18, .mv 50 19, .mv 50 20, .rw 6 7 0 true,
     .rw 4 6 0 false, .rw 1 16 1 true, .mv 12 10, .mv 13 12, .mv 41 17, .mv 41 18, .mv 41 19,
     .mv 41 20, .mv 41 21, .mv 41 22, .mv 41 23, .rw 14 7 0 true, .rw 3 5 1 true,
     .rw 8 7 0 true, .rw 0 31 0 true, .mv 38 12, .mv 38 13, .mv 38 14, .mv 38 15, .mv 38 16,
     .mv 38 17, .mv 38 18, .rw 12 9 1 true, .mv 35 13, .rw 9 9 1 true, .rw 0 35 0 true,
     .mv 42 15, .rw 10 11 1 true, .rw 1 8 1 true, .mv 20 12, .mv 21 14, .rw 16 9 1 true,
     .mv 18 13, .mv 39 17, .mv 39 18, .mv 39 19, .mv 39 20, .mv 39 21, .mv 39 22, .mv 39 23,
     .rw 7 10 1 true, .rw 8 12 0 true, .rw 5 9 1 false, .rw 1 8 0 true, .mv 10 9,
     .rw 3 10 0 true, .mv 13 12, .rw 8 11 0 false, .rw 3 5 1 false, .rw 3 4 0 false, .mv 4 3,
     .rw 1 2 0 false, .rw 1 2 1 false, .rw 3 1 0 false, .rw 3 0 1 false, .rw 2 16 2 false,
     .rw 1 15 2 false, .rw 1 15 2 true, .rw 2 16 2 true, .rw 1 18 2 true, .rw 2 9 1 true,
     .mv 19 9, .mv 20 11, .mv 21 13, .mv 22 14, .rw 13 7 1 true, .rw 5 13 0 true, .mv 13 5,
     .rw 5 14 0 true, .mv 14 6, .rw 5 12 1 true, .mv 12 9, .rw 5 13 1 true, .mv 13 10,
     .rw 1 11 1 true, .rw 1 7 1 true, .mv 15 11, .mv 16 13, .rw 16 8 1 true, .rw 1 7 0 true,
     .rw 2 8 0 true, .rw 0 29 0 true, .mv 36 11, .rw 10 7 0 true, .mv 13 10, .mv 14 11,
     .mv 15 12, .mv 16 13, .rw 15 0 0 true, .mv 3 2, .rw 4 1 0 true, .mv 4 3, .mv 9 6,
     .mv 11 7, .mv 11 8, .mv 12 9, .mv 17 14, .mv 18 15, .mv 19 16, .mv 20 17, .mv 19 18,
     .mv 20 19])
    (by decide +kernel)

/-- Equation 3.57 (supplement: `[ZZ 0 1 B 2 1 2 B 4 0 1]·ω^0 = [B 2 1 2 B 1 0 1 H 1 ZZ 1 2 H 1]·ω^0`). -/
theorem rule_3_57 :
    Holds 3 ([.CZ 1] ++ bB 2 0 ++ bB 4 1)
      (bB 2 0 ++ bB 1 1 ++ [.H 1, .CZ 0, .H 1]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))
    (steps := [.mv 3 2, .mv 8 7, .rw 3 4 0 true, .mv 7 6, .rw 7 7 0 false, .rw 2 9 1 true, .rw 4 8 0 true,
     .rw 5 7 1 true, .mv 7 6, .rw 2 15 2 true, .rw 1 11 1 true, .rw 1 7 1 true, .mv 18 12,
     .mv 19 14, .mv 20 16, .mv 21 17, .rw 16 8 0 true, .mv 11 10, .mv 12 11, .mv 19 18,
     .mv 20 19, .mv 21 20, .mv 27 23, .rw 4 22 1 true, .rw 2 28 2 true, .mv 28 24,
     .rw 4 23 1 true, .mv 29 25, .rw 4 24 1 true, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23,
     .mv 30 27, .mv 31 29, .rw 12 24 1 true, .mv 24 20, .mv 25 21, .mv 26 22,
     .rw 4 18 0 true, .rw 4 19 0 true, .rw 4 20 0 true, .rw 1 19 1 true, .rw 11 12 1 true,
     .rw 1 25 2 true, .mv 12 11, .mv 13 12, .mv 16 15, .mv 23 18, .mv 24 19, .mv 25 20,
     .rw 14 13 1 true, .mv 13 11, .mv 14 12, .mv 17 16, .rw 1 27 2 true, .rw 2 19 1 true,
     .mv 28 19, .mv 29 21, .mv 30 23, .mv 31 24, .rw 10 17 1 true, .rw 2 28 2 true,
     .mv 28 21, .rw 4 20 1 true, .mv 29 22, .rw 4 21 1 true, .rw 1 23 1 true,
     .rw 0 37 0 true, .mv 44 30, .mv 44 31, .mv 44 32, .mv 44 33, .rw 9 24 1 true, .mv 17 16,
     .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20, .mv 32 24, .mv 33 26, .rw 12 21 1 true,
     .mv 21 16, .mv 22 17, .mv 23 18, .rw 5 24 1 true, .mv 24 19, .rw 5 25 1 true, .mv 25 20,
     .rw 1 21 2 true, .mv 38 28, .mv 38 29, .mv 38 30, .mv 38 31, .rw 9 22 2 true, .mv 21 16,
     .mv 22 18, .mv 23 20, .mv 24 21, .rw 10 14 1 true, .rw 1 21 1 true, .mv 13 12,
     .mv 14 13, .mv 15 14, .mv 16 15, .mv 23 19, .mv 24 21, .rw 12 16 1 true, .mv 16 12,
     .mv 17 13, .mv 18 14, .rw 4 10 0 true, .rw 4 11 0 true, .rw 4 12 0 true,
     .rw 1 12 1 true, .rw 0 31 0 true, .mv 38 13, .mv 38 14, .rw 8 9 1 true, .mv 19 10,
     .mv 20 12, .rw 0 39 0 true, .mv 46 16, .mv 46 17, .mv 46 18, .mv 46 19, .mv 46 20,
     .mv 46 21, .mv 46 22, .rw 13 6 1 true, .mv 15 10, .mv 33 14, .mv 33 15, .mv 33 16,
     .mv 33 17, .mv 33 18, .mv 33 19, .mv 33 20, .rw 6 7 1 true, .rw 7 9 0 true,
     .rw 1 6 0 true, .mv 8 7, .rw 3 8 0 true, .mv 11 10, .rw 7 9 0 false, .rw 3 4 0 false,
     .mv 4 3, .rw 1 2 0 false, .rw 1 2 1 false, .rw 3 1 0 false, .rw 3 0 1 false,
     .rw 3 15 1 false, .mv 6 5, .mv 9 8, .mv 14 11, .rw 15 4 1 true, .mv 7 6, .mv 10 9,
     .mv 2 1, .mv 10 9])
    (by decide +kernel)

/-- Equation 3.58 (supplement: `[ZZ 0 1 B 3 1 2 B 1 0 1]·ω^0 = [B 3 1 2 B 4 0 1 H 1 H 2 S 2 H 2 ZZ 1 2 H 1 S 2 H 2 S 2]·ω^7`). -/
theorem rule_3_58 :
    Holds 3 ([.CZ 1] ++ bB 3 0 ++ bB 1 1)
      (bB 3 0 ++ bB 4 1 ++ [.H 1, .H 0, .S 0, .H 0, .CZ 0, .H 1, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))))))
    (steps := [.mv 5 4, .mv 13 12, .rw 4 2 0 false, .mv 4 3, .rw 15 1 0 false, .rw 1 14 1 false,
     .rw 5 13 1 false, .rw 5 12 1 false, .mv 16 13, .rw 16 14 1 false, .mv 14 13, .mv 18 17,
     .mv 20 18, .mv 21 19, .mv 22 20, .rw 1 19 1 false, .mv 19 18, .mv 20 19, .mv 21 20,
     .rw 5 21 1 false, .mv 18 17, .mv 19 18, .mv 20 19, .rw 5 20 1 false, .rw 13 17 1 false,
     .mv 20 19, .mv 22 20, .mv 25 21, .mv 26 22, .rw 2 19 1 false, .mv 14 13, .mv 17 16,
     .rw 19 11 1 false, .mv 13 12, .mv 16 15, .rw 1 18 2 false, .mv 11 6, .mv 12 7, .mv 13 8,
     .mv 14 9, .mv 15 10, .mv 16 11, .mv 17 12, .rw 1 13 2 true, .mv 14 19, .rw 1 13 1 true,
     .mv 14 20, .rw 3 14 0 true, .mv 15 16, .rw 1 15 1 true, .mv 16 17, .rw 3 17 1 true,
     .rw 2 16 2 true, .rw 1 18 2 true, .rw 2 6 0 true, .rw 1 9 0 true, .rw 2 10 0 true,
     .rw 3 0 0 true, .rw 2 1 1 true, .rw 1 2 1 true, .rw 1 1 0 true, .mv 2 4, .rw 3 4 0 true,
     .rw 12 18 0 false, .mv 27 61, .mv 26 60, .mv 25 59, .mv 24 58, .mv 23 57, .mv 22 56,
     .mv 21 55, .rw 8 18 0 false, .mv 22 55, .rw 0 55 0 false, .rw 1 21 0 false,
     .rw 2 18 0 false, .rw 1 30 2 false, .mv 28 25, .mv 29 26, .mv 30 27, .mv 31 28,
     .rw 2 25 2 false, .rw 7 12 0 true, .mv 14 13, .rw 3 11 0 false, .mv 11 7,
     .rw 1 6 0 false, .rw 5 9 1 false, .rw 5 8 1 false, .rw 5 7 1 false, .rw 2 8 1 false,
     .rw 7 9 0 false, .rw 6 7 1 false, .mv 20 45, .mv 19 44, .mv 18 43, .mv 17 42, .mv 16 41,
     .mv 15 40, .mv 14 39, .mv 11 10, .mv 12 11, .mv 13 12, .mv 14 13, .mv 15 14,
     .rw 17 6 1 false, .mv 22 51, .mv 21 50, .mv 20 49, .mv 19 48, .mv 18 47, .mv 17 46,
     .mv 16 45, .rw 0 51 0 false, .mv 11 10, .mv 13 11, .mv 14 12, .mv 15 13, .mv 16 14,
     .mv 17 15, .mv 18 16, .mv 19 17, .mv 20 18, .rw 10 9 1 false, .mv 14 44, .mv 13 43,
     .rw 0 43 0 false, .rw 1 12 1 false, .rw 4 12 0 false, .rw 4 11 0 false,
     .rw 4 10 0 false, .mv 15 12, .mv 16 13, .mv 17 14, .mv 18 15, .rw 16 16 1 false,
     .mv 16 12, .mv 20 19, .mv 22 20, .mv 23 21, .mv 24 22, .rw 1 21 1 false,
     .rw 13 14 1 false, .mv 17 16, .mv 19 17, .mv 22 18, .mv 23 19, .mv 24 20,
     .rw 11 22 2 false, .mv 31 50, .mv 30 49, .mv 29 48, .mv 28 47, .mv 21 16, .mv 22 17,
     .rw 1 16 2 false, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23, .mv 25 24,
     .rw 5 25 1 false, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23,
     .rw 5 24 1 false, .mv 19 16, .mv 20 17, .mv 21 18, .mv 22 19, .mv 23 20,
     .rw 16 21 1 false, .mv 21 16, .mv 25 24, .mv 27 25, .mv 28 26, .mv 29 27, .mv 30 28,
     .mv 31 29, .mv 32 30, .mv 33 31, .rw 11 24 1 false, .mv 33 52, .mv 32 51, .mv 31 50,
     .mv 30 49, .rw 0 49 0 false, .rw 1 23 1 false, .rw 4 21 1 false, .mv 23 22, .mv 24 23,
     .mv 25 24, .mv 26 25, .mv 27 26, .mv 28 27, .mv 29 28, .rw 4 20 1 false, .mv 22 21,
     .mv 23 22, .mv 24 23, .mv 25 24, .mv 26 25, .mv 27 26, .mv 28 27, .mv 28 21, .mv 29 22,
     .mv 30 23, .mv 31 24, .rw 2 21 2 false, .rw 13 17 1 false, .mv 20 19, .mv 22 20,
     .mv 25 21, .mv 26 22, .mv 27 23, .mv 28 24, .mv 29 25, .mv 30 26, .mv 31 27,
     .rw 2 19 1 false, .rw 1 27 2 false, .mv 13 11, .mv 14 12, .mv 17 16, .rw 18 13 1 false,
     .mv 13 11, .mv 16 15, .mv 21 18, .mv 22 19, .mv 23 20, .mv 24 21, .mv 25 22,
     .rw 1 25 2 false, .rw 14 12 1 false, .rw 1 19 1 false, .rw 4 20 0 false,
     .rw 4 19 0 false, .rw 4 18 0 false, .mv 23 20, .mv 24 21, .mv 25 22, .mv 26 23,
     .rw 16 24 1 false, .mv 24 20, .mv 28 27, .mv 30 28, .mv 31 29, .rw 4 24 1 false,
     .mv 26 25, .mv 27 26, .mv 28 27, .mv 29 28, .rw 4 23 1 false, .mv 25 24, .mv 26 25,
     .mv 27 26, .mv 28 27, .mv 28 24, .mv 29 25, .mv 30 26, .mv 31 27, .rw 2 24 2 false,
     .rw 4 22 1 false, .mv 24 23, .mv 25 24, .mv 26 25, .mv 27 26, .mv 12 10, .mv 21 18,
     .rw 20 8 0 false, .mv 13 12, .mv 15 13, .mv 18 14, .mv 19 15, .mv 20 16, .mv 21 17,
     .rw 1 7 1 false, .rw 1 11 1 false, .rw 2 15 2 false, .mv 7 6, .rw 5 7 1 false,
     .rw 4 8 0 false, .rw 2 9 1 false, .rw 7 7 0 true, .mv 7 6, .rw 3 4 0 false,
     .rw 2 10 1 true, .mv 22 10, .mv 23 12, .mv 24 14, .mv 25 15, .rw 13 8 1 true,
     .rw 5 15 0 true, .mv 15 5, .rw 5 16 0 true, .mv 16 6, .rw 5 13 1 true, .mv 13 10,
     .rw 5 14 1 true, .mv 14 11, .rw 1 12 1 true, .rw 1 7 1 true, .mv 9 8, .mv 16 12,
     .mv 17 14, .rw 16 9 1 true, .mv 9 8, .mv 10 9, .mv 11 10, .rw 1 7 0 true,
     .rw 2 8 0 true, .rw 0 28 0 true, .mv 35 11, .rw 9 7 0 true, .mv 13 10, .mv 14 11,
     .mv 15 12, .mv 16 13, .rw 15 0 0 true, .mv 3 2, .rw 4 1 0 true, .mv 4 3, .mv 9 6,
     .mv 10 7, .mv 12 8, .mv 12 9, .mv 13 10, .mv 14 11, .mv 19 16])
    (by decide +kernel)

/-- Equation 3.59 (supplement: `[ZZ 0 1 B 3 1 2 B 2 0 1]·ω^0 = [B 2 1 2 B 3 0 1 H 1 S 1 H 1 ZZ 1 2 X 0 S 1 H 2 S 2]·ω^7`). -/
theorem rule_3_59 :
    Holds 3 ([.CZ 1] ++ bB 3 0 ++ bB 2 1)
      (bB 2 0 ++ bB 3 1 ++ [.H 1, .S 1, .H 1, .CZ 0] ++ bX 2 ++ [.S 1, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [.mv 5 4, .mv 9 8, .rw 4 2 0 false, .mv 4 3, .rw 15 1 0 false, .rw 16 12 1 false, .mv 16 15,
     .mv 18 16, .mv 19 17, .mv 20 18, .mv 11 6, .mv 12 7, .rw 1 6 1 false, .rw 1 15 1 false,
     .mv 15 14, .mv 16 15, .mv 17 16, .rw 5 17 1 false, .mv 14 13, .mv 15 14, .mv 16 15,
     .rw 5 16 1 false, .rw 13 13 1 false, .mv 16 15, .mv 18 16, .mv 21 17, .mv 22 18,
     .rw 2 15 1 false, .rw 3 0 0 true, .rw 1 1 1 true, .rw 1 1 0 true, .mv 2 3,
     .rw 3 3 0 true, .rw 3 4 1 true, .rw 2 5 2 true, .rw 1 6 2 true, .rw 1 5 1 true, .mv 6 8,
     .rw 3 8 1 true, .rw 3 9 0 true, .rw 4 16 1 false, .mv 18 17, .mv 19 18, .mv 20 19,
     .mv 21 20, .rw 4 15 1 false, .mv 17 16, .mv 18 17, .mv 19 18, .mv 20 19,
     .rw 4 14 1 false, .mv 16 15, .mv 17 16, .mv 18 17, .mv 19 18, .rw 8 22 0 true,
     .mv 22 19, .mv 24 20, .rw 3 18 0 false, .mv 18 17, .rw 1 16 0 false, .rw 5 20 1 true,
     .mv 20 17, .mv 29 24, .rw 8 23 0 false, .rw 7 21 1 false, .mv 34 47, .mv 33 46,
     .mv 32 45, .mv 31 44, .mv 30 43, .mv 29 42, .mv 28 41, .mv 21 18, .mv 22 19, .mv 25 24,
     .mv 26 25, .mv 27 26, .mv 28 27, .mv 29 28, .mv 30 29, .mv 31 30, .mv 32 31, .mv 33 32,
     .mv 34 33, .mv 20 17, .mv 21 18, .mv 22 19, .rw 16 20 1 false, .mv 20 17, .mv 24 23,
     .mv 26 24, .mv 27 25, .mv 28 26, .mv 29 27, .mv 30 28, .mv 31 29, .mv 32 30, .mv 33 31,
     .mv 34 32, .mv 35 33, .mv 36 34, .mv 37 35, .rw 1 16 1 false, .rw 10 22 1 false,
     .mv 26 43, .rw 0 43 0 false, .rw 9 20 1 false, .mv 24 43, .rw 12 20 1 false, .mv 29 45,
     .mv 28 44, .mv 27 43, .mv 26 42, .mv 25 41, .mv 24 40, .mv 23 39, .rw 0 39 0 false,
     .rw 4 18 1 false, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23, .mv 25 24,
     .mv 26 25, .mv 27 26, .mv 28 27, .mv 29 28, .mv 29 19, .mv 30 20, .mv 31 21, .mv 32 22,
     .rw 2 19 2 false, .rw 4 17 1 false, .mv 19 18, .mv 20 19, .mv 21 20, .mv 22 21,
     .mv 23 22, .mv 24 23, .mv 25 24, .mv 26 25, .mv 27 26, .mv 28 27, .rw 4 16 1 false,
     .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23, .mv 25 24,
     .mv 26 25, .mv 27 26, .rw 8 15 0 false, .rw 3 14 1 false, .mv 14 13, .mv 15 14,
     .mv 16 15, .mv 17 16, .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22,
     .mv 24 23, .rw 14 14 0 false, .mv 30 45, .mv 29 44, .mv 28 43, .mv 27 42, .mv 26 41,
     .mv 25 40, .mv 24 39, .mv 18 17, .mv 20 18, .mv 24 19, .mv 25 20, .mv 26 21, .mv 27 22,
     .mv 28 23, .rw 2 17 0 false, .rw 1 24 1 false, .rw 4 13 0 true, .rw 6 14 0 false,
     .mv 27 43, .mv 26 42, .mv 25 41, .mv 24 40, .mv 23 39, .mv 22 38, .mv 21 37,
     .rw 0 43 0 false, .mv 21 18, .mv 22 19, .mv 23 20, .rw 11 21 1 false, .mv 26 36,
     .mv 25 35, .rw 0 35 0 false, .rw 13 13 0 false, .mv 16 15, .mv 18 16, .mv 21 17,
     .mv 22 18, .mv 23 19, .mv 24 20, .rw 1 12 1 false, .rw 2 13 0 false, .rw 1 18 1 false,
     .rw 2 16 1 false, .mv 15 13, .mv 16 14, .rw 1 13 1 false, .mv 16 15, .mv 17 16,
     .mv 18 17, .mv 19 18, .rw 5 19 1 false, .rw 13 16 1 false, .mv 19 18, .mv 21 19,
     .mv 24 20, .mv 15 12, .mv 16 13, .rw 1 12 2 false, .rw 1 22 2 false, .rw 2 20 2 false,
     .mv 19 16, .mv 20 17, .rw 1 16 2 false, .rw 8 11 0 true, .mv 13 12, .mv 14 13,
     .rw 3 9 0 false, .mv 12 10, .mv 13 11, .rw 3 10 1 false, .mv 12 10, .rw 4 9 0 true,
     .mv 13 11, .rw 4 10 0 true, .rw 1 15 2 true, .rw 2 16 2 true, .rw 1 18 2 true,
     .rw 1 11 1 true, .rw 2 12 1 true, .rw 0 29 0 true, .mv 36 15, .rw 10 11 1 true,
     .mv 21 14, .mv 22 15, .mv 23 16, .mv 24 17, .rw 15 4 1 true, .mv 7 6, .rw 4 5 1 true,
     .mv 2 1, .mv 8 7, .mv 17 14, .mv 18 15, .mv 19 16, .mv 20 17, .mv 20 18])
    (by decide +kernel)

/-- Equation 3.60 (supplement: `[ZZ 0 1 B 3 1 2 B 3 0 1]·ω^0 = [B 2 1 2 B 2 0 1 ZZ 1 2 H 1 S 1 H 2 S 2]·ω^0`). -/
theorem rule_3_60 :
    Holds 3 ([.CZ 1] ++ bB 3 0 ++ bB 3 1)
      (bB 2 0 ++ bB 2 1 ++ [.CZ 0, .H 1, .S 1, .H 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil)))))))))))))))))
    (steps := [.mv 5 4, .mv 11 10, .rw 4 2 0 false, .mv 4 3, .rw 15 1 0 false, .mv 15 12, .mv 16 13,
     .rw 16 14 1 false, .mv 14 12, .mv 18 17, .mv 20 18, .mv 21 19, .mv 22 20, .mv 11 6,
     .mv 12 7, .rw 1 6 1 false, .rw 1 17 1 false, .rw 4 12 1 false, .mv 14 13, .mv 15 14,
     .mv 16 15, .mv 16 15, .mv 17 16, .mv 18 17, .mv 19 18, .rw 5 19 1 false, .mv 15 14,
     .mv 16 15, .mv 17 16, .mv 18 17, .rw 5 18 1 false, .rw 13 15 1 false, .mv 18 17,
     .mv 20 18, .mv 23 19, .mv 24 20, .rw 2 17 1 false, .rw 15 11 1 false, .rw 1 24 2 false,
     .rw 2 22 2 false, .mv 21 16, .mv 22 17, .rw 1 16 2 false, .rw 2 10 0 true,
     .rw 3 0 0 true, .rw 1 1 1 true, .rw 1 1 0 true, .mv 2 3, .rw 3 3 0 true, .rw 3 4 1 true,
     .rw 1 5 2 true, .rw 1 5 1 true, .mv 6 7, .rw 3 7 1 true, .rw 12 22 0 false, .mv 31 43,
     .mv 30 42, .mv 29 41, .mv 28 40, .mv 27 39, .mv 26 38, .mv 25 37, .rw 9 22 0 false,
     .mv 26 37, .rw 0 37 0 false, .rw 8 16 0 true, .mv 18 17, .rw 3 15 0 false, .mv 15 14,
     .rw 1 13 0 false, .rw 5 14 1 true, .mv 23 18, .rw 8 17 0 false, .rw 7 15 1 false,
     .mv 28 43, .mv 27 42, .mv 26 41, .mv 25 40, .mv 24 39, .mv 23 38, .mv 22 37, .mv 19 18,
     .mv 20 19, .mv 21 20, .mv 22 21, .mv 23 22, .mv 24 23, .mv 25 24, .mv 26 25, .mv 27 26,
     .mv 28 27, .rw 16 14 1 false, .mv 18 17, .mv 20 18, .mv 21 19, .mv 22 20, .mv 23 21,
     .mv 24 22, .mv 25 23, .mv 26 24, .mv 27 25, .mv 28 26, .mv 29 27, .mv 30 28, .mv 31 29,
     .rw 1 13 1 false, .rw 10 16 1 false, .mv 20 39, .rw 0 39 0 false, .rw 9 14 1 false,
     .mv 18 39, .rw 12 14 1 false, .mv 23 41, .mv 22 40, .mv 21 39, .mv 20 38, .mv 19 37,
     .mv 18 36, .mv 17 35, .rw 0 35 0 false, .mv 24 14, .mv 25 15, .mv 26 16, .mv 27 17,
     .rw 2 14 2 false, .rw 8 12 0 false, .rw 3 11 1 false, .mv 11 10, .mv 12 11, .mv 13 12,
     .mv 14 13, .mv 15 14, .mv 16 15, .mv 17 16, .mv 18 17, .mv 19 18, .mv 20 19, .mv 21 20,
     .mv 21 9, .mv 22 10, .rw 1 9 2 false, .rw 14 11 0 false, .mv 27 39, .mv 26 38,
     .mv 25 37, .mv 24 36, .mv 23 35, .mv 22 34, .mv 21 33, .mv 15 14, .mv 17 15, .mv 21 16,
     .mv 22 17, .mv 23 18, .mv 24 19, .mv 25 20, .rw 2 14 0 false, .rw 1 21 1 false,
     .rw 4 10 0 true, .rw 6 11 0 false, .mv 24 37, .mv 23 36, .mv 22 35, .mv 21 34,
     .mv 20 33, .mv 19 32, .mv 18 31, .rw 0 37 0 false, .mv 18 15, .mv 19 16, .mv 20 17,
     .rw 11 18 1 false, .mv 23 30, .mv 22 29, .rw 0 29 0 false, .rw 13 10 0 false, .mv 13 12,
     .mv 15 13, .mv 18 14, .mv 19 15, .mv 20 16, .mv 21 17, .rw 1 9 1 false,
     .rw 2 10 0 false, .rw 1 15 1 false, .rw 2 13 1 false, .mv 12 10, .mv 13 11,
     .rw 1 10 1 false, .rw 5 12 1 false, .rw 2 13 1 false, .mv 12 10, .rw 8 9 0 false,
     .rw 3 7 1 false, .mv 2 1, .mv 6 5, .mv 11 9, .mv 12 10])
    (by decide +kernel)

end QCert.SelingerClifford
