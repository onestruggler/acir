/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): rewrite rules, part 4

Equations 3.61–3.80 of the supplement to Selinger's paper (the rewrite
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

/-- Equation 3.61 (supplement: `[ZZ 0 1 B 3 1 2 B 4 0 1]·ω^0 = [B 3 1 2 B 1 0 1 H 1 H 2 S 2 H 2 ZZ 1 2 H 1 S 2 H 2 S 2]·ω^7`). -/
theorem rule_3_61 :
    Holds 3 ([Lt.CZ 1] ++ bB 3 0 ++ bB 4 1)
      (bB 3 0 ++ bB 1 1 ++ [.H 1, .H 0, .S 0, .H 0, .CZ 0, .H 1, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL8 (db_ok_cons hL14 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM18 (db_ok_cons hM21 db_ok_nil)))))))))))))))))))
    (steps := [Step.mv 5 4, Step.mv 10 9, Step.rw 4 2 0 false, Step.mv 4 3, Step.rw 13 1 0 false, Step.mv 15 12, Step.rw 14 13 1 false,
     Step.mv 13 12, Step.mv 17 16, Step.mv 19 17, Step.mv 20 18, Step.mv 21 19, Step.mv 11 6, Step.mv 12 7,
     Step.rw 1 6 1 false, Step.rw 1 16 1 false, Step.mv 16 15, Step.mv 17 16, Step.mv 18 17, Step.rw 5 18 1 false,
     Step.mv 15 14, Step.mv 16 15, Step.mv 17 16, Step.rw 5 17 1 false, Step.rw 11 14 1 false, Step.mv 17 16,
     Step.mv 19 17, Step.mv 22 18, Step.mv 23 19, Step.rw 2 16 1 false, Step.rw 3 5 0 true, Step.mv 13 7, Step.mv 14 9,
     Step.rw 7 8 0 false, Step.rw 2 15 1 true, Step.mv 15 10, Step.rw 4 9 0 true, Step.rw 5 8 1 true, Step.mv 8 7,
     Step.rw 2 21 2 true, Step.rw 1 17 1 true, Step.rw 1 8 1 true, Step.mv 24 13, Step.mv 19 14, Step.mv 25 15,
     Step.mv 21 16, Step.mv 26 17, Step.mv 27 18, Step.rw 18 9 0 true, Step.mv 12 11, Step.mv 13 12, Step.mv 20 19,
     Step.mv 24 20, Step.mv 25 21, Step.mv 26 22, Step.mv 27 23, Step.mv 28 24, Step.mv 26 25, Step.mv 27 26, Step.mv 33 29,
     Step.rw 4 28 1 true, Step.rw 2 34 2 true, Step.mv 34 30, Step.rw 4 29 1 true, Step.mv 35 31,
     Step.rw 4 30 1 true, Step.mv 27 26, Step.mv 28 27, Step.mv 29 28, Step.mv 30 29, Step.mv 36 33, Step.mv 37 35,
     Step.rw 14 30 1 true, Step.mv 30 26, Step.mv 31 27, Step.mv 32 28, Step.mv 25 20, Step.rw 4 19 0 true,
     Step.mv 26 21, Step.rw 4 20 0 true, Step.mv 27 22, Step.rw 4 21 0 true, Step.rw 1 20 1 true,
     Step.rw 12 13 1 true, Step.rw 1 31 2 true, Step.mv 13 12, Step.mv 14 13, Step.mv 17 16, Step.mv 29 19,
     Step.mv 30 20, Step.mv 31 21, Step.rw 16 14 1 true, Step.mv 14 12, Step.mv 15 13, Step.mv 18 17,
     Step.rw 1 33 2 true, Step.rw 2 20 1 true, Step.mv 34 20, Step.mv 35 22, Step.mv 36 24, Step.mv 37 25,
     Step.rw 11 18 1 true, Step.rw 2 34 2 true, Step.mv 34 22, Step.rw 4 21 1 true, Step.mv 35 23,
     Step.rw 4 22 1 true, Step.rw 1 24 1 true, Step.rw 0 47 0 true, Step.mv 54 31, Step.mv 54 32, Step.mv 54 33,
     Step.mv 54 34, Step.rw 10 25 1 true, Step.mv 18 17, Step.mv 19 18, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21,
     Step.mv 38 25, Step.mv 39 27, Step.rw 14 22 1 true, Step.mv 22 17, Step.mv 23 18, Step.mv 24 19,
     Step.rw 5 25 1 true, Step.mv 25 20, Step.rw 5 26 1 true, Step.mv 26 21, Step.rw 1 22 2 true, Step.mv 48 29,
     Step.mv 48 30, Step.mv 48 31, Step.mv 48 32, Step.rw 10 23 2 true, Step.mv 22 17, Step.mv 23 19, Step.mv 24 21,
     Step.mv 25 22, Step.rw 11 15 1 true, Step.rw 1 22 1 true, Step.mv 14 13, Step.mv 15 14, Step.mv 16 15,
     Step.mv 17 16, Step.mv 24 20, Step.mv 25 22, Step.rw 14 17 1 true, Step.mv 17 13, Step.mv 18 14, Step.mv 19 15,
     Step.rw 4 11 0 true, Step.rw 4 12 0 true, Step.rw 4 13 0 true, Step.rw 1 13 1 true, Step.rw 0 41 0 true,
     Step.mv 48 14, Step.mv 48 15, Step.rw 9 10 1 true, Step.mv 20 11, Step.mv 21 13, Step.rw 0 49 0 true, Step.mv 56 17,
     Step.mv 56 18, Step.mv 56 19, Step.mv 56 20, Step.mv 56 21, Step.mv 56 22, Step.mv 56 23, Step.rw 15 7 1 true,
     Step.mv 16 11, Step.mv 43 15, Step.mv 43 16, Step.mv 43 17, Step.mv 43 18, Step.mv 43 19, Step.mv 43 20, Step.mv 43 21,
     Step.rw 6 8 1 true, Step.rw 7 10 0 true, Step.rw 2 9 1 true, Step.rw 5 8 1 true, Step.rw 5 9 1 true,
     Step.rw 5 10 1 true, Step.rw 1 7 0 true, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11,
     Step.rw 3 12 0 true, Step.mv 15 14, Step.rw 7 13 0 false, Step.rw 2 34 2 true, Step.rw 1 36 2 true,
     Step.rw 3 5 0 false, Step.mv 5 3, Step.rw 1 2 0 false, Step.rw 1 3 1 false, Step.rw 2 2 1 false,
     Step.rw 3 1 0 false, Step.rw 3 0 1 false, Step.rw 1 22 2 false, Step.rw 2 20 2 false, Step.rw 3 21 1 false,
     Step.rw 1 20 2 false, Step.rw 1 20 2 true, Step.mv 7 6, Step.mv 10 9, Step.mv 20 12, Step.rw 17 5 1 true,
     Step.mv 8 7, Step.mv 11 10, Step.rw 2 13 1 true, Step.mv 25 13, Step.mv 26 15, Step.mv 27 17, Step.mv 28 18,
     Step.rw 11 11 1 true, Step.rw 5 18 0 true, Step.mv 18 5, Step.rw 5 19 0 true, Step.mv 19 6, Step.rw 5 16 1 true,
     Step.mv 16 13, Step.rw 5 17 1 true, Step.mv 17 14, Step.rw 1 15 1 true, Step.mv 10 9, Step.mv 17 13, Step.mv 18 15,
     Step.rw 14 10 1 true, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.rw 5 8 1 true, Step.rw 5 9 1 true,
     Step.rw 1 10 1 true, Step.rw 1 7 0 true, Step.rw 2 8 0 true, Step.rw 0 31 0 true, Step.mv 38 11,
     Step.rw 8 7 0 true, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12, Step.mv 16 13, Step.rw 13 0 0 true, Step.mv 3 2,
     Step.rw 4 1 0 true, Step.mv 4 3, Step.mv 9 6, Step.mv 10 7, Step.mv 11 8, Step.mv 12 9, Step.mv 13 10, Step.mv 15 11,
     Step.mv 15 12, Step.mv 16 13, Step.mv 17 14, Step.mv 22 19])
    (by decide +kernel)

/-- Equation 3.62 (supplement: `[ZZ 0 1 B 4 1 2 B 1 0 1]·ω^0 = [B 4 1 2 B 1 0 1 H 1 H 2 ZZ 1 2 H 1 H 2]·ω^0`). -/
theorem rule_3_62 :
    Holds 3 ([Lt.CZ 1] ++ bB 4 0 ++ bB 1 1)
      (bB 4 0 ++ bB 1 1 ++ [.H 1, .H 0, .CZ 0, .H 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 (db_ok_cons hM18 (db_ok_cons hM20 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 4 3, Step.mv 12 11, Step.mv 9 8, Step.mv 12 11, Step.rw 16 6 1 false, Step.mv 8 7, Step.mv 11 10, Step.rw 1 6 2 true,
     Step.rw 3 7 1 true, Step.rw 1 8 2 true, Step.rw 1 8 1 true, Step.mv 10 9, Step.rw 3 10 1 true,
     Step.rw 1 11 1 true, Step.rw 1 6 0 true, Step.mv 8 2, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11,
     Step.mv 13 12, Step.rw 17 1 0 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.rw 2 14 1 true, Step.rw 1 15 1 true, Step.rw 12 8 1 true, Step.rw 2 21 2 true, Step.mv 21 14,
     Step.rw 4 13 1 true, Step.mv 22 15, Step.rw 4 14 1 true, Step.mv 23 16, Step.rw 4 15 1 true,
     Step.rw 2 24 2 true, Step.rw 1 20 1 true, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.mv 15 14, Step.mv 26 18,
     Step.mv 27 20, Step.rw 13 15 1 true, Step.mv 15 11, Step.mv 16 12, Step.mv 17 13, Step.rw 0 40 0 true,
     Step.mv 47 18, Step.rw 9 14 2 true, Step.mv 14 12, Step.mv 15 13, Step.mv 16 14, Step.mv 46 15, Step.mv 46 16,
     Step.mv 46 17, Step.mv 46 18, Step.mv 46 19, Step.mv 46 20, Step.mv 46 21, Step.rw 5 8 1 true, Step.rw 1 23 2 true,
     Step.rw 0 38 0 true, Step.mv 45 24, Step.rw 8 20 2 true, Step.mv 44 23, Step.mv 44 24, Step.mv 44 25, Step.mv 44 26,
     Step.mv 44 27, Step.mv 44 28, Step.mv 44 29, Step.rw 11 20 2 true, Step.rw 2 16 1 true, Step.rw 1 18 1 true,
     Step.mv 13 11, Step.mv 26 15, Step.mv 27 16, Step.mv 28 17, Step.mv 29 18, Step.mv 30 19, Step.rw 15 10 1 true,
     Step.mv 10 9, Step.mv 13 12, Step.mv 14 13, Step.rw 1 19 1 true, Step.rw 0 42 0 true, Step.mv 49 20, Step.mv 49 21,
     Step.rw 10 16 1 true, Step.mv 14 12, Step.mv 27 17, Step.mv 28 19, Step.rw 0 50 0 true, Step.mv 57 23,
     Step.mv 57 24, Step.mv 57 25, Step.mv 57 26, Step.mv 57 27, Step.mv 57 28, Step.mv 57 29, Step.rw 14 13 1 true,
     Step.mv 13 12, Step.mv 14 13, Step.mv 15 14, Step.mv 15 13, Step.mv 23 17, Step.mv 44 21, Step.mv 44 22, Step.mv 44 23,
     Step.mv 44 24, Step.mv 44 25, Step.mv 44 26, Step.mv 44 27, Step.rw 6 14 1 true, Step.rw 7 16 0 true, Step.mv 18 17,
     Step.mv 20 19, Step.mv 23 22, Step.rw 16 18 1 true, Step.mv 21 20, Step.mv 24 23, Step.rw 1 19 2 true,
     Step.rw 3 0 1 false, Step.rw 1 17 2 false, Step.rw 3 23 1 false, Step.mv 23 22, Step.rw 1 21 1 false,
     Step.rw 1 21 2 false, Step.rw 3 20 1 false, Step.mv 20 19, Step.rw 1 18 1 false, Step.rw 1 18 2 false,
     Step.rw 3 17 1 false, Step.mv 8 7, Step.mv 11 10, Step.mv 17 13, Step.rw 16 6 1 true, Step.mv 9 8, Step.mv 12 11,
     Step.mv 3 2, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9, Step.mv 12 10, Step.mv 12 11, Step.mv 13 12,
     Step.mv 14 13, Step.mv 17 16])
    (by decide +kernel)

/-- Equation 3.63 (supplement: `[ZZ 0 1 B 4 1 2 B 2 0 1]·ω^0 = [B 1 1 2 B 2 0 1 H 2 ZZ 1 2 H 2]·ω^0`). -/
theorem rule_3_63 :
    Holds 3 ([Lt.CZ 1] ++ bB 4 0 ++ bB 2 1)
      (bB 1 0 ++ bB 2 1 ++ [.H 0, .CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 4 3, Step.mv 8 7, Step.rw 2 7 1 true, Step.rw 5 6 1 true, Step.rw 4 5 0 true, Step.rw 1 9 1 true,
     Step.rw 1 7 0 true, Step.rw 2 8 0 true, Step.rw 1 6 1 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6,
     Step.mv 15 9, Step.mv 16 11, Step.mv 17 13, Step.rw 14 6 0 true, Step.mv 8 7, Step.mv 13 12, Step.mv 16 15,
     Step.rw 5 20 0 true, Step.mv 20 16, Step.rw 2 22 0 true, Step.rw 5 21 0 true, Step.mv 21 17,
     Step.rw 5 22 0 true, Step.mv 22 18, Step.rw 5 20 1 true, Step.mv 27 24, Step.mv 28 26, Step.mv 29 28, Step.mv 30 29,
     Step.rw 11 22 0 true, Step.rw 5 21 1 true, Step.rw 5 22 1 true, Step.rw 1 21 1 true, Step.mv 8 7, Step.mv 9 8,
     Step.mv 10 9, Step.mv 13 12, Step.mv 19 15, Step.mv 20 16, Step.mv 21 17, Step.rw 16 10 0 true, Step.mv 10 7,
     Step.mv 11 8, Step.mv 14 13, Step.rw 0 29 0 true, Step.mv 36 20, Step.rw 8 16 0 true, Step.rw 5 15 0 true,
     Step.mv 15 14, Step.mv 35 20, Step.mv 35 21, Step.mv 35 22, Step.mv 35 23, Step.mv 35 24, Step.mv 35 25, Step.mv 35 26,
     Step.rw 10 17 0 true, Step.rw 5 16 0 true, Step.mv 16 15, Step.rw 1 27 1 true, Step.mv 24 18, Step.mv 25 20,
     Step.mv 26 22, Step.mv 27 23, Step.rw 11 16 0 true, Step.rw 1 16 0 true, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10,
     Step.mv 18 14, Step.mv 19 16, Step.rw 15 11 0 true, Step.mv 11 8, Step.mv 12 9, Step.mv 13 10, Step.rw 1 20 0 true,
     Step.rw 13 13 0 true, Step.rw 5 12 1 true, Step.rw 1 21 0 true, Step.rw 13 14 0 true, Step.rw 5 13 1 true,
     Step.rw 1 22 0 true, Step.rw 13 15 0 true, Step.rw 5 14 1 true, Step.mv 27 25, Step.rw 3 26 1 true,
     Step.rw 7 27 0 true, Step.mv 29 28, Step.rw 1 14 1 true, Step.rw 0 33 0 true, Step.mv 40 15, Step.mv 40 16,
     Step.rw 9 11 1 true, Step.mv 11 7, Step.mv 12 9, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13, Step.rw 0 41 0 true,
     Step.mv 48 14, Step.mv 48 15, Step.mv 48 16, Step.mv 48 17, Step.mv 48 18, Step.mv 48 19, Step.mv 48 20,
     Step.rw 12 4 0 true, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.mv 35 12, Step.mv 35 13, Step.mv 35 14,
     Step.mv 35 15, Step.mv 35 16, Step.mv 35 17, Step.mv 35 18, Step.rw 6 5 0 true, Step.mv 9 8, Step.rw 7 7 0 false,
     Step.rw 1 3 1 false, Step.rw 3 2 0 false, Step.rw 1 1 1 false, Step.rw 3 0 1 false, Step.rw 3 15 1 false,
     Step.mv 2 1, Step.mv 5 4, Step.mv 8 7, Step.rw 17 0 0 true, Step.mv 3 2, Step.mv 6 5, Step.mv 6 5, Step.mv 9 8,
     Step.mv 11 9, Step.mv 11 10, Step.mv 12 11])
    (by decide +kernel)

/-- Equation 3.64 (supplement: `[ZZ 0 1 B 4 1 2 B 3 0 1]·ω^0 = [B 1 1 2 B 3 0 1 H 2 H 1 S 1 H 1 ZZ 2 1 S 1 H 1 S 1 H 2]·ω^7`). -/
theorem rule_3_64 :
    Holds 3 ([Lt.CZ 1] ++ bB 4 0 ++ bB 3 1)
      (bB 1 0 ++ bB 3 1 ++ [.H 0, .H 1, .S 1, .H 1, .CZ 0, .S 1, .H 1, .S 1, .H 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hL21 (db_ok_cons hM14 (db_ok_cons hM16 (db_ok_cons hM18 db_ok_nil))))))))))))))))))))
    (steps := [Step.mv 4 3, Step.mv 10 9, Step.rw 4 7 1 false, Step.mv 9 8, Step.rw 15 6 1 false, Step.rw 2 7 1 true,
     Step.rw 5 6 1 true, Step.rw 4 5 0 true, Step.rw 1 9 1 true, Step.rw 1 7 0 true, Step.rw 2 8 0 true,
     Step.rw 1 6 1 true, Step.rw 1 3 0 true, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 17 11,
     Step.mv 18 13, Step.mv 19 15, Step.rw 16 8 0 true, Step.mv 10 9, Step.mv 15 14, Step.mv 18 17, Step.rw 5 22 0 true,
     Step.mv 22 18, Step.rw 2 24 0 true, Step.rw 5 23 0 true, Step.mv 23 19, Step.rw 5 24 0 true, Step.mv 24 20,
     Step.rw 5 22 1 true, Step.mv 29 26, Step.mv 30 28, Step.mv 31 30, Step.mv 32 31, Step.rw 12 24 0 true,
     Step.rw 5 23 1 true, Step.rw 5 24 1 true, Step.rw 1 23 1 true, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11,
     Step.mv 15 14, Step.mv 21 17, Step.mv 22 18, Step.mv 23 19, Step.rw 18 12 0 true, Step.mv 12 9, Step.mv 13 10,
     Step.mv 16 15, Step.rw 0 41 0 true, Step.mv 48 22, Step.rw 9 18 0 true, Step.rw 5 17 0 true, Step.mv 17 16,
     Step.mv 47 22, Step.mv 47 23, Step.mv 47 24, Step.mv 47 25, Step.mv 47 26, Step.mv 47 27, Step.mv 47 28,
     Step.rw 11 19 0 true, Step.rw 5 18 0 true, Step.mv 18 17, Step.rw 1 29 1 true, Step.mv 26 20, Step.mv 27 22,
     Step.mv 28 24, Step.mv 29 25, Step.rw 12 18 0 true, Step.rw 1 18 0 true, Step.mv 11 10, Step.mv 12 11,
     Step.mv 13 12, Step.mv 20 16, Step.mv 21 18, Step.rw 17 13 0 true, Step.mv 13 10, Step.mv 14 11, Step.mv 15 12,
     Step.rw 1 22 0 true, Step.rw 14 15 0 true, Step.rw 5 14 1 true, Step.rw 1 23 0 true, Step.rw 14 16 0 true,
     Step.rw 5 15 1 true, Step.rw 1 24 0 true, Step.rw 14 17 0 true, Step.rw 5 16 1 true, Step.mv 29 27,
     Step.mv 30 28, Step.rw 3 29 1 true, Step.rw 7 30 0 true, Step.mv 32 31, Step.rw 1 16 1 true,
     Step.rw 0 45 0 true, Step.mv 52 17, Step.mv 52 18, Step.rw 10 13 1 true, Step.mv 13 9, Step.mv 14 11, Step.mv 15 13,
     Step.mv 16 14, Step.mv 17 15, Step.rw 0 53 0 true, Step.mv 60 16, Step.mv 60 17, Step.mv 60 18, Step.mv 60 19,
     Step.mv 60 20, Step.mv 60 21, Step.mv 60 22, Step.rw 13 6 0 true, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13,
     Step.mv 47 14, Step.mv 47 15, Step.mv 47 16, Step.mv 47 17, Step.mv 47 18, Step.mv 47 19, Step.mv 47 20,
     Step.rw 6 7 0 true, Step.mv 11 10, Step.rw 7 9 0 false, Step.rw 1 26 2 true, Step.rw 2 27 2 true,
     Step.rw 1 29 2 true, Step.rw 2 26 1 true, Step.rw 1 29 1 true, Step.rw 0 51 0 true, Step.mv 58 30,
     Step.rw 8 26 1 true, Step.mv 57 29, Step.mv 57 30, Step.mv 57 31, Step.mv 57 32, Step.mv 57 33, Step.mv 57 34,
     Step.mv 57 35, Step.rw 11 26 1 true, Step.rw 1 3 0 false, Step.rw 1 3 1 false, Step.rw 3 2 0 false,
     Step.rw 1 1 1 false, Step.rw 3 0 1 false, Step.rw 2 20 1 false, Step.rw 1 19 1 false, Step.rw 2 16 1 false,
     Step.rw 1 19 2 false, Step.rw 2 17 2 false, Step.rw 1 16 2 false, Step.rw 3 16 1 false, Step.mv 2 1,
     Step.mv 5 4, Step.mv 8 7, Step.rw 19 0 0 true, Step.mv 3 2, Step.mv 6 5, Step.mv 16 15, Step.rw 4 14 0 true,
     Step.mv 17 16, Step.rw 4 15 0 true, Step.rw 1 16 1 true, Step.rw 2 17 1 true, Step.rw 0 31 0 true,
     Step.mv 38 20, Step.rw 9 16 1 true, Step.mv 27 19, Step.mv 28 20, Step.mv 29 21, Step.mv 30 22, Step.rw 15 9 1 true,
     Step.mv 12 11, Step.rw 4 10 1 true, Step.mv 6 5, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 13 11, Step.mv 13 12,
     Step.mv 14 13, Step.mv 20 19, Step.mv 21 20, Step.mv 22 21])
    (by decide +kernel)

/-- Equation 3.65 (supplement: `[ZZ 0 1 B 4 1 2 B 4 0 1]·ω^0 = [B 4 1 2 B 4 0 1 H 1 H 2 ZZ 1 2 H 1 H 2]·ω^0`). -/
theorem rule_3_65 :
    Holds 3 ([Lt.CZ 1] ++ bB 4 0 ++ bB 4 1)
      (bB 4 0 ++ bB 4 1 ++ [.H 1, .H 0, .CZ 0, .H 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hM20 db_ok_nil)))
    (steps := [Step.mv 4 3, Step.mv 9 8, Step.rw 0 11 1 true, Step.rw 0 6 0 true, Step.mv 7 13, Step.rw 1 13 0 true, Step.mv 7 2,
     Step.rw 2 0 0 false, Step.mv 2 1, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 3 2, Step.mv 6 5, Step.mv 7 6,
     Step.mv 9 7, Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 14 13])
    (by decide +kernel)

/-- Equation 3.66 (supplement: `[H 1 D 1 0 1]·ω^0 = [D 1 0 1 H 0]·ω^0`). -/
theorem rule_3_66 :
    Holds 2 ([Lt.H 0] ++ bD 1 0)
      (bD 1 0 ++ [.H 1]) :=
  Holds.of_derives (db_ok_cons hM18 db_ok_nil)
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.mv 3 2, Step.mv 6 5, Step.rw 0 0 0 false, Step.mv 2 1, Step.mv 5 4, Step.mv 8 7, Step.mv 2 1,
     Step.mv 5 4])
    (by decide +kernel)

/-- Equation 3.67 (supplement: `[H 1 D 2 0 1]·ω^0 = [D 4 0 1]·ω^0`). -/
theorem rule_3_67 :
    Holds 2 ([Lt.H 0] ++ bD 2 0)
      (bD 4 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [Step.mv 4 3, Step.mv 1 0, Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.68 (supplement: `[H 1 D 3 0 1]·ω^0 = [D 3 0 1 S 0 S 0 S 0 H 0 S 0 S 1 S 1]·ω^0`). -/
theorem rule_3_68 :
    Holds 2 ([Lt.H 0] ++ bD 3 0)
      (bD 3 0 ++ [.S 1, .S 1, .S 1, .H 1, .S 1, .S 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hL4 (db_ok_cons hL10 (db_ok_cons hM17 db_ok_nil)))))))
    (steps := [Step.mv 2 1, Step.mv 3 2, Step.mv 6 5, Step.rw 1 0 0 false, Step.mv 1 0, Step.rw 3 1 0 false, Step.rw 2 7 1 true,
     Step.rw 1 10 1 true, Step.rw 0 13 0 true, Step.mv 20 11, Step.rw 4 7 1 true, Step.mv 19 10, Step.mv 19 11,
     Step.mv 19 12, Step.mv 19 13, Step.mv 19 14, Step.mv 19 15, Step.mv 19 16, Step.rw 5 7 1 true, Step.rw 2 7 0 true,
     Step.rw 1 9 0 true, Step.mv 4 2, Step.mv 13 6, Step.mv 14 7, Step.mv 15 8, Step.mv 16 9, Step.mv 17 10,
     Step.rw 6 1 0 true, Step.mv 1 0, Step.mv 4 3, Step.mv 5 4, Step.rw 3 2 0 true, Step.mv 2 1, Step.mv 2 0, Step.mv 5 4,
     Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.mv 13 11, Step.mv 14 12])
    (by decide +kernel)

/-- Equation 3.69 (supplement: `[H 1 D 4 0 1]·ω^0 = [D 2 0 1]·ω^0`). -/
theorem rule_3_69 :
    Holds 2 ([Lt.H 0] ++ bD 4 0)
      (bD 2 0) :=
  Holds.of_derives (db_ok_cons hC2 db_ok_nil)
    (steps := [Step.mv 2 1, Step.mv 5 4, Step.rw 0 0 0 false, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.70 (supplement: `[S 1 D 1 0 1]·ω^0 = [D 1 0 1 H 0 S 0 H 0]·ω^0`). -/
theorem rule_3_70 :
    Holds 2 ([Lt.S 0] ++ bD 1 0)
      (bD 1 0 ++ [.H 1, .S 1, .H 1]) :=
  Holds.of_derives (db_ok_cons hC7 (db_ok_cons hM16 db_ok_nil))
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.rw 0 0 0 false, Step.mv 3 1, Step.mv 6 5, Step.rw 1 2 0 false, Step.mv 2 1, Step.mv 5 4,
     Step.mv 10 7, Step.mv 2 1, Step.mv 5 4])
    (by decide +kernel)

/-- Equation 3.71 (supplement: `[S 1 D 2 0 1]·ω^0 = [D 3 0 1 S 0 S 0 S 0 H 0 S 0 S 1 S 1]·ω^0`). -/
theorem rule_3_71 :
    Holds 2 ([Lt.S 0] ++ bD 2 0)
      (bD 3 0 ++ [.S 1, .S 1, .S 1, .H 1, .S 1, .S 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hL4 (db_ok_cons hL10 (db_ok_cons hM17 db_ok_nil)))))))
    (steps := [Step.mv 4 3, Step.mv 1 0, Step.rw 3 1 0 false, Step.rw 2 7 1 true, Step.rw 1 10 1 true, Step.rw 0 13 0 true,
     Step.mv 20 11, Step.rw 4 7 1 true, Step.mv 19 10, Step.mv 19 11, Step.mv 19 12, Step.mv 19 13, Step.mv 19 14,
     Step.mv 19 15, Step.mv 19 16, Step.rw 5 7 1 true, Step.rw 2 7 0 true, Step.rw 1 9 0 true, Step.mv 4 2, Step.mv 13 6,
     Step.mv 14 7, Step.mv 15 8, Step.mv 16 9, Step.mv 17 10, Step.rw 6 1 0 true, Step.mv 1 0, Step.mv 4 3, Step.mv 5 4,
     Step.rw 3 2 0 true, Step.mv 2 1, Step.mv 2 0, Step.mv 5 4, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.mv 13 11,
     Step.mv 14 12])
    (by decide +kernel)

/-- Equation 3.72 (supplement: `[S 1 D 3 0 1]·ω^0 = [D 2 0 1 S 0 H 0 S 0]·ω^0`). -/
theorem rule_3_72 :
    Holds 2 ([Lt.S 0] ++ bD 3 0)
      (bD 2 0 ++ [.S 1, .H 1, .S 1]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC7 (db_ok_cons hM14 (db_ok_cons hM17 db_ok_nil)))))
    (steps := [Step.mv 2 1, Step.mv 3 2, Step.mv 6 5, Step.mv 3 2, Step.rw 2 3 0 false, Step.mv 2 1, Step.mv 6 4, Step.rw 4 2 0 false,
     Step.mv 4 3, Step.mv 5 4, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10, Step.mv 16 11, Step.rw 0 10 0 false,
     Step.mv 1 0, Step.rw 2 1 0 false, Step.mv 5 2, Step.rw 3 3 0 false, Step.mv 3 2, Step.mv 7 6, Step.mv 9 7, Step.mv 10 8,
     Step.mv 11 9, Step.mv 12 10, Step.mv 13 11, Step.rw 0 8 0 false, Step.rw 1 6 0 false, Step.mv 6 5, Step.mv 7 6,
     Step.mv 8 7, Step.mv 9 8, Step.rw 1 5 1 false, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.73 (supplement: `[S 1 D 4 0 1]·ω^0 = [D 4 0 1 H 0 S 0 H 0]·ω^0`). -/
theorem rule_3_73 :
    Holds 2 ([Lt.S 0] ++ bD 4 0)
      (bD 4 0 ++ [.H 1, .S 1, .H 1]) :=
  Holds.of_derives (db_ok_cons hM16 db_ok_nil)
    (steps := [Step.mv 2 1, Step.mv 5 4, Step.mv 2 0, Step.mv 5 4, Step.rw 0 1 0 false, Step.mv 1 0, Step.mv 4 3, Step.mv 9 6, Step.mv 1 0,
     Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.74 (supplement: `[S 0 D 1 0 1]·ω^0 = [D 1 0 1 S 1]·ω^0`). -/
theorem rule_3_74 :
    Holds 2 ([Lt.S 1] ++ bD 1 0)
      (bD 1 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC6 (db_ok_cons hL16 db_ok_nil)))
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.rw 1 0 0 false, Step.mv 2 1, Step.rw 2 2 0 false, Step.rw 0 9 0 false, Step.mv 2 1,
     Step.mv 5 4])
    (by decide +kernel)

/-- Equation 3.75 (supplement: `[S 0 D 2 0 1]·ω^0 = [D 2 0 1 S 1]·ω^0`). -/
theorem rule_3_75 :
    Holds 2 ([Lt.S 1] ++ bD 2 0)
      (bD 2 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL16 db_ok_nil))
    (steps := [Step.mv 4 3, Step.rw 1 0 0 false, Step.rw 0 7 0 false, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.76 (supplement: `[S 0 D 3 0 1]·ω^0 = [D 3 0 1 S 1]·ω^0`). -/
theorem rule_3_76 :
    Holds 2 ([Lt.S 1] ++ bD 3 0)
      (bD 3 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL16 db_ok_nil))
    (steps := [Step.mv 2 0, Step.mv 3 1, Step.mv 6 5, Step.rw 1 2 0 false, Step.rw 0 9 0 false, Step.mv 2 0, Step.mv 5 4])
    (by decide +kernel)

/-- Equation 3.77 (supplement: `[S 0 D 4 0 1]·ω^0 = [D 4 0 1 S 1]·ω^0`). -/
theorem rule_3_77 :
    Holds 2 ([Lt.S 1] ++ bD 4 0)
      (bD 4 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL16 db_ok_nil))
    (steps := [Step.mv 2 0, Step.mv 5 4, Step.rw 1 1 0 false, Step.rw 0 8 0 false, Step.mv 1 0, Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.78 (supplement: `[ZZ 0 1 D 1 0 1]·ω^0 = [D 4 0 1]·ω^0`). -/
theorem rule_3_78 :
    Holds 2 ([Lt.CZ 0] ++ bD 1 0)
      (bD 4 0) :=
  Holds.of_derives (db_ok_cons hC5 db_ok_nil)
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.rw 0 0 0 false, Step.mv 1 0, Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.79 (supplement: `[ZZ 0 1 D 2 0 1]·ω^0 = [D 3 0 1 S 0 S 0 S 0 H 0 S 1 S 1 S 1]·ω^0`). -/
theorem rule_3_79 :
    Holds 2 ([Lt.CZ 0] ++ bD 2 0)
      (bD 3 0 ++ [.S 1, .S 1, .S 1, .H 1, .S 0, .S 0, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL10 (db_ok_cons hL16 (db_ok_cons hM17 db_ok_nil)))))))))))
    (steps := [Step.mv 4 3, Step.rw 5 0 0 false, Step.mv 13 17, Step.mv 12 16, Step.mv 11 15, Step.mv 10 14, Step.mv 9 13, Step.mv 8 12,
     Step.mv 7 11, Step.mv 7 4, Step.rw 7 5 1 false, Step.mv 9 11, Step.rw 0 11 0 false, Step.rw 3 8 0 false,
     Step.mv 10 9, Step.rw 3 7 0 false, Step.mv 9 8, Step.rw 3 6 0 false, Step.mv 8 7, Step.rw 4 2 0 true, Step.mv 2 0,
     Step.rw 9 1 0 false, Step.rw 1 8 0 false, Step.mv 1 0, Step.rw 4 1 0 false, Step.rw 1 11 1 true,
     Step.rw 0 13 0 true, Step.mv 20 12, Step.rw 6 8 1 true, Step.mv 19 11, Step.mv 19 12, Step.mv 19 13, Step.mv 19 14,
     Step.mv 19 15, Step.mv 19 16, Step.mv 19 17, Step.rw 8 8 1 true, Step.rw 2 7 0 true, Step.rw 1 9 0 true,
     Step.mv 4 2, Step.mv 14 6, Step.mv 15 7, Step.mv 16 8, Step.mv 17 9, Step.mv 18 10, Step.rw 10 1 0 true, Step.mv 1 0,
     Step.mv 4 3, Step.mv 5 4, Step.rw 4 2 0 true, Step.mv 2 1, Step.mv 2 0, Step.mv 5 4, Step.mv 11 8, Step.mv 12 9,
     Step.mv 13 10, Step.mv 14 11])
    (by decide +kernel)

/-- Equation 3.80 (supplement: `[ZZ 0 1 D 3 0 1]·ω^0 = [D 2 0 1 H 0 S 0 S 1]·ω^0`). -/
theorem rule_3_80 :
    Holds 2 ([Lt.CZ 0] ++ bD 3 0)
      (bD 2 0 ++ [.H 1, .S 1, .S 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hL5 (db_ok_cons hL16 (db_ok_cons hM14 (db_ok_cons hM17 db_ok_nil))))))))))
    (steps := [Step.mv 2 1, Step.mv 3 2, Step.mv 6 5, Step.mv 3 2, Step.rw 4 3 0 false, Step.mv 2 1, Step.mv 6 4, Step.rw 9 2 0 false,
     Step.mv 4 3, Step.mv 5 4, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10, Step.mv 16 11, Step.rw 1 10 0 false,
     Step.rw 5 0 0 false, Step.mv 13 25, Step.mv 12 24, Step.mv 11 23, Step.mv 10 22, Step.mv 9 21, Step.mv 8 20,
     Step.mv 7 19, Step.mv 7 4, Step.mv 8 5, Step.rw 6 6 1 false, Step.mv 10 19, Step.rw 0 19 0 false, Step.mv 6 3,
     Step.mv 7 4, Step.mv 8 5, Step.mv 9 6, Step.rw 8 7 0 false, Step.mv 7 3, Step.mv 11 10, Step.mv 13 11, Step.mv 14 12,
     Step.mv 15 13, Step.mv 16 14, Step.mv 17 15, Step.rw 1 12 0 false, Step.rw 2 10 0 false, Step.mv 10 9,
     Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.rw 2 9 1 false, Step.rw 3 7 0 false, Step.mv 9 8,
     Step.rw 3 6 0 false, Step.mv 8 7, Step.rw 3 5 0 false, Step.mv 7 6, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.rw 2 6 1 false, Step.rw 7 0 0 false, Step.rw 1 7 0 false, Step.mv 3 2, Step.mv 7 6, Step.mv 8 7])
    (by decide +kernel)

end QCert.SelingerClifford
