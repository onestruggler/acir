/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): rewrite rules, part 1

Equations 3.1–3.20 of the supplement to Selinger's paper (the rewrite
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

/-- Equation 3.1 (supplement: `[]·ω^0 = [A 1 0 C 1 0 E 1 0]·ω^0`). -/
theorem rule_3_1 :
    Holds 1 ([])
      (bA 1 0 ++ bC 1 0 ++ bE 1 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.2 (supplement: `[C 1 1]·ω^0 = [B 1 0 1 C 1 0 D 1 0 1]·ω^0`). -/
theorem rule_3_2 :
    Holds 2 (bC 1 0)
      (bB 1 0 ++ bC 1 1 ++ bD 1 0) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 db_ok_nil))
    (steps := [Step.rw 0 0 0 true, Step.rw 1 1 0 true, Step.rw 0 2 1 true, Step.rw 0 2 0 true, Step.mv 4 3, Step.rw 1 4 0 true,
     Step.rw 0 5 1 true, Step.rw 0 5 0 true, Step.mv 7 6, Step.rw 1 7 0 true, Step.mv 6 5, Step.mv 10 9, Step.mv 13 12])
    (by decide +kernel)

/-- Equation 3.3 (supplement: `[H 0 A 1 0]·ω^0 = [A 2 0]·ω^0`). -/
theorem rule_3_3 :
    Holds 1 ([Lt.H 0] ++ bA 1 0)
      (bA 2 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.4 (supplement: `[H 0 A 2 0]·ω^0 = [A 1 0]·ω^0`). -/
theorem rule_3_4 :
    Holds 1 ([Lt.H 0] ++ bA 2 0)
      (bA 1 0) :=
  Holds.of_derives (db_ok_cons hC2 db_ok_nil)
    (steps := [Step.rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.5 (supplement: `[H 0 A 3 0]·ω^0 = [A 3 0 X 0 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_5 :
    Holds 1 ([Lt.H 0] ++ bA 3 0)
      (bA 3 0 ++ bX 0 ++ [.S 0, .S 0, .S 0, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL6 db_ok_nil))))
    (steps := [Step.rw 1 0 0 false, Step.rw 2 2 0 true, Step.rw 0 6 0 true, Step.mv 13 3, Step.mv 13 4, Step.mv 13 5, Step.mv 13 6,
     Step.mv 13 7, Step.mv 13 8, Step.mv 13 9, Step.rw 3 0 0 true, Step.rw 1 2 0 true])
    (by decide +kernel)

/-- Equation 3.6 (supplement: `[S 0 A 1 0]·ω^0 = [A 1 0 S 0]·ω^0`). -/
theorem rule_3_6 :
    Holds 1 ([Lt.S 0] ++ bA 1 0)
      (bA 1 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.7 (supplement: `[S 0 A 2 0]·ω^0 = [A 3 0 X 0 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_7 :
    Holds 1 ([Lt.S 0] ++ bA 2 0)
      (bA 3 0 ++ bX 0 ++ [.S 0, .S 0, .S 0, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL6 db_ok_nil))))
    (steps := [Step.rw 2 2 0 true, Step.rw 0 6 0 true, Step.mv 13 3, Step.mv 13 4, Step.mv 13 5, Step.mv 13 6, Step.mv 13 7, Step.mv 13 8,
     Step.mv 13 9, Step.rw 3 0 0 true, Step.rw 1 2 0 true])
    (by decide +kernel)

/-- Equation 3.8 (supplement: `[S 0 A 3 0]·ω^0 = [A 2 0 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_8 :
    Holds 1 ([Lt.S 0] ++ bA 3 0)
      (bA 2 0 ++ [.S 0, .S 0, .S 0, .om]) :=
  Holds.of_derives (db_ok_cons hL5 db_ok_nil)
    (steps := [Step.rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.9 (supplement: `[ZZ 0 1 A 1 0]·ω^0 = [A 1 0 ZZ 0 1]·ω^0`). -/
theorem rule_3_9 :
    Holds 2 ([Lt.CZ 0] ++ bA 1 1)
      (bA 1 1 ++ [.CZ 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.10 (supplement: `[ZZ 0 1 A 2 0]·ω^0 = [A 1 1 B 2 0 1 ZZ 0 1 H 1]·ω^0`). -/
theorem rule_3_10 :
    Holds 2 ([Lt.CZ 0] ++ bA 2 1)
      (bA 1 0 ++ bB 2 0 ++ [.CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 db_ok_nil))
    (steps := [Step.rw 0 1 0 true, Step.mv 3 2, Step.rw 1 3 0 true, Step.mv 2 1])
    (by decide +kernel)

/-- Equation 3.11 (supplement: `[ZZ 0 1 A 3 0]·ω^0 = [A 1 1 B 3 0 1 H 1 S 1 H 1 ZZ 0 1 S 0 S 0 S 0 H 1]·ω^0`). -/
theorem rule_3_11 :
    Holds 2 ([Lt.CZ 0] ++ bA 3 1)
      (bA 1 0 ++ bB 3 0 ++ [.H 0, .S 0, .H 0, .CZ 0, .S 1, .S 1, .S 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hL5 (db_ok_cons hL9 (db_ok_cons hL14 (db_ok_cons hL17 db_ok_nil))))))))))
    (steps := [Step.rw 2 2 1 true, Step.rw 0 8 0 true, Step.mv 15 5, Step.rw 6 1 1 true, Step.rw 1 1 0 true, Step.mv 3 2, Step.mv 4 3,
     Step.rw 3 4 0 true, Step.mv 18 12, Step.mv 18 13, Step.mv 18 14, Step.mv 18 15, Step.mv 18 16, Step.mv 18 17,
     Step.rw 7 7 1 true, Step.rw 2 6 0 true, Step.rw 1 5 1 true, Step.mv 13 8, Step.mv 14 10, Step.mv 15 12,
     Step.mv 16 13, Step.rw 8 6 0 true, Step.rw 5 9 0 true, Step.mv 9 5, Step.rw 5 10 0 true, Step.mv 10 6,
     Step.rw 1 7 0 true, Step.rw 2 8 0 true, Step.mv 22 11, Step.rw 6 7 0 true, Step.mv 13 10, Step.mv 14 11,
     Step.mv 15 12, Step.mv 16 13, Step.rw 9 0 0 true, Step.mv 3 2, Step.rw 4 1 0 true, Step.mv 4 3, Step.mv 11 10,
     Step.mv 12 11, Step.mv 13 12])
    (by decide +kernel)

/-- Equation 3.12 (supplement: `[ZZ 0 1 A 1 1 B 1 0 1]·ω^0 = [A 1 1 B 1 0 1 H 1 ZZ 0 1 H 1]·ω^0`). -/
theorem rule_3_12 :
    Holds 2 ([Lt.CZ 0] ++ bA 1 0 ++ bB 1 0)
      (bA 1 0 ++ bB 1 0 ++ [.H 0, .CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL18 (db_ok_cons hM18 db_ok_nil)))
    (steps := [Step.mv 7 6, Step.rw 0 9 0 true, Step.rw 1 2 0 true, Step.mv 2 1, Step.mv 5 4, Step.mv 8 7, Step.rw 2 0 0 true, Step.mv 3 2,
     Step.mv 6 5, Step.mv 6 5])
    (by decide +kernel)

/-- Equation 3.13 (supplement: `[ZZ 0 1 A 1 1 B 2 0 1]·ω^0 = [A 2 0 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_13 :
    Holds 2 ([Lt.CZ 0] ++ bA 1 0 ++ bB 2 0)
      (bA 2 1 ++ [.H 0, .CZ 0]) :=
  Holds.of_derives (db_ok_cons hC5 db_ok_nil)
    (steps := [Step.mv 3 2, Step.rw 0 0 0 false, Step.mv 1 0])
    (by decide +kernel)

/-- Equation 3.14 (supplement: `[ZZ 0 1 A 1 1 B 3 0 1]·ω^0 = [A 3 0 H 1 ZZ 0 1 S 0 S 1 H 1 S 1]·ω^7`). -/
theorem rule_3_14 :
    Holds 2 ([Lt.CZ 0] ++ bA 1 0 ++ bB 3 0)
      (bA 3 1 ++ [.H 0, .CZ 0, .S 1, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL8 (db_ok_cons hL9 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hM14 db_ok_nil))))))))))))))
    (steps := [Step.mv 5 4, Step.rw 2 2 0 false, Step.mv 4 3, Step.rw 4 0 0 false, Step.mv 13 17, Step.mv 12 16, Step.mv 11 15,
     Step.mv 10 14, Step.mv 9 13, Step.mv 8 12, Step.mv 7 11, Step.mv 7 4, Step.rw 11 7 0 false, Step.mv 10 9, Step.mv 12 10,
     Step.rw 1 6 1 false, Step.rw 2 5 0 false, Step.mv 7 6, Step.mv 8 7, Step.rw 3 2 0 true, Step.mv 2 0,
     Step.rw 5 3 0 false, Step.mv 16 23, Step.mv 15 22, Step.mv 14 21, Step.mv 13 20, Step.mv 12 19, Step.mv 11 18,
     Step.mv 10 17, Step.rw 0 23 0 false, Step.mv 3 1, Step.mv 4 2, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.mv 11 10, Step.rw 8 11 1 false, Step.rw 0 19 0 false, Step.mv 3 0, Step.mv 4 1, Step.rw 13 2 0 false,
     Step.mv 2 0, Step.mv 6 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.mv 13 11, Step.mv 14 12,
     Step.rw 7 6 0 false, Step.mv 10 21, Step.rw 6 4 0 false, Step.mv 8 21, Step.rw 10 4 0 false, Step.mv 13 23,
     Step.mv 12 22, Step.mv 11 21, Step.mv 10 20, Step.mv 9 19, Step.mv 8 18, Step.mv 7 17, Step.rw 0 20 0 false,
     Step.rw 6 4 0 false, Step.mv 8 17, Step.rw 8 9 1 false, Step.mv 18 20, Step.mv 17 19, Step.mv 16 18, Step.mv 15 17,
     Step.rw 0 17 0 false, Step.rw 9 9 1 false, Step.mv 19 20, Step.mv 18 19, Step.mv 17 18, Step.mv 16 17,
     Step.mv 15 16, Step.mv 14 15, Step.mv 9 4, Step.mv 10 6, Step.mv 11 8, Step.mv 12 9, Step.mv 13 10, Step.rw 0 21 0 true,
     Step.mv 28 11, Step.mv 28 12, Step.mv 28 13, Step.mv 28 14, Step.mv 28 15, Step.mv 28 16, Step.mv 28 17,
     Step.rw 12 1 0 true, Step.mv 1 0, Step.mv 2 1, Step.mv 3 2, Step.mv 8 5])
    (by decide +kernel)

/-- Equation 3.15 (supplement: `[ZZ 0 1 A 1 1 B 4 0 1]·ω^0 = [A 1 1 B 4 0 1 H 1 ZZ 0 1 S 1 S 1 H 1]·ω^0`). -/
theorem rule_3_15 :
    Holds 2 ([Lt.CZ 0] ++ bA 1 0 ++ bB 4 0)
      (bA 1 0 ++ bB 4 0 ++ [.H 0, .CZ 0, .S 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL16 (db_ok_cons hM15 db_ok_nil))))))))))))
    (steps := [Step.mv 4 3, Step.rw 3 0 0 false, Step.mv 13 16, Step.mv 12 15, Step.mv 11 14, Step.mv 10 13, Step.mv 9 12, Step.mv 8 11,
     Step.mv 7 10, Step.mv 7 4, Step.rw 6 5 1 false, Step.mv 9 10, Step.rw 0 10 0 false, Step.rw 1 8 0 false,
     Step.rw 1 7 0 false, Step.rw 1 6 0 false, Step.rw 2 2 0 true, Step.mv 2 0, Step.rw 10 1 0 false, Step.mv 1 0,
     Step.rw 2 1 0 false, Step.rw 0 12 0 true, Step.mv 19 9, Step.mv 19 10, Step.mv 19 11, Step.mv 19 12, Step.mv 19 13,
     Step.mv 19 14, Step.mv 19 15, Step.rw 9 6 0 true, Step.mv 16 10, Step.rw 5 6 0 true, Step.rw 0 16 0 true,
     Step.mv 23 12, Step.rw 6 8 0 true, Step.mv 22 10, Step.mv 22 11, Step.rw 8 6 0 true, Step.mv 4 2, Step.mv 15 7,
     Step.mv 16 9, Step.rw 0 23 0 true, Step.mv 30 13, Step.mv 30 14, Step.mv 30 15, Step.mv 30 16, Step.mv 30 17,
     Step.mv 30 18, Step.mv 30 19, Step.rw 11 3 0 true, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.rw 0 18 0 true,
     Step.mv 25 11, Step.mv 25 12, Step.mv 25 13, Step.mv 25 14, Step.mv 25 15, Step.mv 25 16, Step.mv 25 17,
     Step.rw 7 8 0 true, Step.mv 5 3, Step.mv 13 7, Step.mv 20 11, Step.mv 20 12, Step.mv 20 13, Step.mv 20 14,
     Step.mv 20 15, Step.mv 20 16, Step.mv 20 17, Step.rw 4 4 0 true, Step.mv 3 2])
    (by decide +kernel)

/-- Equation 3.16 (supplement: `[ZZ 0 1 A 2 1 B 1 0 1]·ω^0 = [A 2 1 B 4 0 1]·ω^0`). -/
theorem rule_3_16 :
    Holds 2 ([Lt.CZ 0] ++ bA 2 0 ++ bB 1 0)
      (bA 2 0 ++ bB 4 0) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 db_ok_nil))
    (steps := [Step.mv 8 7, Step.rw 0 1 0 false, Step.rw 1 0 0 false, Step.mv 4 3])
    (by decide +kernel)

/-- Equation 3.17 (supplement: `[ZZ 0 1 A 2 1 B 2 0 1]·ω^0 = [A 3 1 B 3 0 1 H 1 ZZ 0 1 S 0 S 1 S 1 H 1 S 1]·ω^6`). -/
theorem rule_3_17 :
    Holds 2 ([Lt.CZ 0] ++ bA 2 0 ++ bB 2 0)
      (bA 3 0 ++ bB 3 0 ++ [.H 0, .CZ 0, .S 1, .S 0, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))))))))
    (steps := [Step.mv 4 3, Step.rw 5 0 0 false, Step.mv 13 16, Step.mv 12 15, Step.mv 11 14, Step.mv 10 13, Step.mv 9 12, Step.mv 8 11,
     Step.mv 7 10, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.rw 7 3 0 false, Step.mv 7 10,
     Step.rw 0 10 0 false, Step.mv 7 6, Step.mv 8 7, Step.rw 4 8 0 false, Step.mv 6 5, Step.mv 7 6, Step.rw 4 7 0 false,
     Step.mv 5 4, Step.mv 6 5, Step.rw 4 6 0 false, Step.rw 1 10 1 true, Step.rw 2 11 1 true, Step.rw 1 13 1 true,
     Step.mv 10 7, Step.mv 11 9, Step.mv 12 11, Step.mv 13 12, Step.rw 10 5 0 true, Step.rw 4 8 0 true, Step.mv 8 4,
     Step.rw 2 10 0 true, Step.rw 4 9 0 true, Step.mv 9 5, Step.rw 4 10 0 true, Step.mv 10 6, Step.rw 0 18 0 true,
     Step.mv 25 7, Step.rw 7 3 0 true, Step.mv 7 3, Step.mv 24 7, Step.mv 24 8, Step.mv 24 9, Step.mv 24 10, Step.mv 24 11,
     Step.mv 24 12, Step.mv 24 13, Step.rw 5 0 0 true, Step.mv 4 3, Step.rw 3 2 0 true, Step.rw 1 10 0 true,
     Step.rw 2 11 0 true, Step.rw 0 20 0 true, Step.mv 27 14, Step.rw 7 10 0 true, Step.mv 16 13, Step.mv 17 14,
     Step.mv 18 15, Step.mv 19 16, Step.rw 11 3 0 true, Step.rw 2 12 1 true, Step.mv 12 9, Step.rw 3 8 0 true,
     Step.mv 22 13, Step.mv 22 14, Step.mv 22 15, Step.mv 22 16, Step.mv 22 17, Step.mv 22 18, Step.mv 22 19,
     Step.rw 9 10 0 true, Step.rw 0 20 0 true, Step.mv 27 14, Step.rw 6 10 0 true, Step.mv 26 16,
     Step.rw 7 12 0 true, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.mv 17 11, Step.mv 18 13, Step.rw 12 8 0 true,
     Step.mv 8 5, Step.mv 9 6, Step.mv 10 7, Step.rw 4 11 0 true, Step.mv 11 8, Step.rw 2 13 0 true, Step.rw 4 12 0 true,
     Step.mv 12 9, Step.rw 4 13 0 true, Step.mv 13 10, Step.rw 0 26 0 true, Step.mv 33 14, Step.mv 33 15, Step.mv 33 16,
     Step.mv 33 17, Step.mv 33 18, Step.mv 33 19, Step.mv 33 20, Step.rw 8 11 1 true, Step.rw 1 14 1 true, Step.mv 30 11,
     Step.rw 7 7 0 true, Step.mv 11 10, Step.mv 12 11, Step.mv 13 12, Step.mv 14 13, Step.rw 11 0 0 true,
     Step.rw 0 22 0 true, Step.mv 29 10, Step.mv 29 11, Step.mv 29 12, Step.mv 29 13, Step.mv 29 14, Step.mv 29 15,
     Step.mv 29 16, Step.rw 9 7 1 true, Step.rw 2 7 0 true, Step.rw 1 9 0 true, Step.mv 3 2, Step.mv 4 3, Step.mv 13 7,
     Step.mv 14 9, Step.rw 12 4 0 true, Step.mv 4 2, Step.mv 5 3, Step.mv 6 4, Step.mv 5 2, Step.rw 3 1 0 true,
     Step.rw 4 2 0 true, Step.mv 2 0, Step.mv 28 16, Step.rw 7 12 1 true, Step.rw 2 14 1 true, Step.mv 31 17,
     Step.rw 7 13 1 true, Step.rw 1 11 0 true, Step.mv 6 4, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10, Step.mv 16 11,
     Step.mv 17 12, Step.rw 14 3 0 true, Step.mv 3 1, Step.mv 6 5, Step.mv 7 6, Step.rw 3 3 0 false, Step.mv 5 4,
     Step.mv 6 5, Step.rw 2 9 0 true, Step.mv 14 9, Step.mv 15 11, Step.mv 16 13, Step.mv 17 14, Step.rw 10 7 0 true,
     Step.rw 4 10 0 true, Step.mv 10 6, Step.rw 4 11 0 true, Step.mv 11 7, Step.mv 8 4, Step.rw 3 3 0 true,
     Step.rw 1 9 0 true, Step.mv 2 0, Step.mv 3 1, Step.mv 11 6, Step.mv 12 8, Step.rw 0 27 0 true, Step.mv 34 12,
     Step.mv 34 13, Step.mv 34 14, Step.mv 34 15, Step.mv 34 16, Step.mv 34 17, Step.mv 34 18, Step.rw 13 2 0 true,
     Step.mv 2 0, Step.mv 3 1, Step.mv 4 2, Step.mv 7 6, Step.mv 15 11])
    (by decide +kernel)

/-- Equation 3.18 (supplement: `[ZZ 0 1 A 2 1 B 3 0 1]·ω^0 = [A 3 1 B 2 0 1 X 0 H 1 ZZ 0 1 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_18 :
    Holds 2 ([Lt.CZ 0] ++ bA 2 0 ++ bB 3 0)
      (bA 3 0 ++ bB 2 0 ++ bX 1 ++ [.H 0, .CZ 0, .S 1, .S 1, .S 1, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hL14 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))
    (steps := [Step.mv 6 5, Step.rw 3 3 0 false, Step.mv 5 4, Step.rw 2 8 1 true, Step.rw 3 7 0 true, Step.rw 2 5 1 true,
     Step.rw 2 5 0 true, Step.rw 1 7 0 true, Step.mv 2 1, Step.mv 11 5, Step.mv 12 7, Step.rw 6 2 0 true, Step.mv 2 1,
     Step.mv 3 2, Step.mv 4 3, Step.rw 4 0 0 true, Step.rw 1 9 0 true, Step.mv 4 2, Step.mv 11 6, Step.mv 12 7, Step.mv 13 8,
     Step.mv 14 9, Step.mv 15 10, Step.rw 8 1 0 true, Step.mv 4 3, Step.mv 5 4, Step.rw 1 8 1 true, Step.rw 2 9 1 true,
     Step.rw 1 11 1 true, Step.rw 2 7 0 true, Step.mv 12 7, Step.mv 13 9, Step.mv 14 11, Step.mv 15 12,
     Step.rw 5 5 0 true, Step.rw 4 8 0 true, Step.mv 8 5, Step.rw 4 9 0 true, Step.mv 9 6, Step.rw 1 7 0 true,
     Step.mv 9 4, Step.mv 10 6, Step.rw 0 22 0 true, Step.mv 29 10, Step.mv 29 11, Step.mv 29 12, Step.mv 29 13,
     Step.mv 29 14, Step.mv 29 15, Step.mv 29 16, Step.rw 7 0 0 true, Step.mv 5 4, Step.mv 8 7, Step.mv 9 8, Step.mv 10 9,
     Step.mv 11 10])
    (by decide +kernel)

/-- Equation 3.19 (supplement: `[ZZ 0 1 A 2 1 B 4 0 1]·ω^0 = [A 2 1 B 1 0 1]·ω^0`). -/
theorem rule_3_19 :
    Holds 2 ([Lt.CZ 0] ++ bA 2 0 ++ bB 4 0)
      (bA 2 0 ++ bB 1 0) :=
  Holds.of_derives (db_ok_cons hC2 db_ok_nil)
    (steps := [Step.mv 5 4, Step.rw 0 0 0 true, Step.mv 7 6])
    (by decide +kernel)

/-- Equation 3.20 (supplement: `[ZZ 0 1 A 3 1 B 1 0 1]·ω^0 = [A 3 1 B 4 0 1 H 1 ZZ 0 1 S 1 H 1]·ω^0`). -/
theorem rule_3_20 :
    Holds 2 ([Lt.CZ 0] ++ bA 3 0 ++ bB 1 0)
      (bA 3 0 ++ bB 4 0 ++ [.H 0, .CZ 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL8 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil))))))))))))))))))
    (steps := [Step.mv 10 9, Step.rw 1 3 0 false, Step.rw 4 2 0 false, Step.rw 6 0 0 false, Step.mv 13 20, Step.mv 12 19, Step.mv 11 18,
     Step.mv 10 17, Step.mv 9 16, Step.mv 8 15, Step.mv 7 14, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.mv 8 5, Step.mv 9 6, Step.rw 15 7 0 false, Step.mv 7 5, Step.mv 11 10, Step.mv 13 11, Step.mv 14 12, Step.mv 15 13,
     Step.rw 1 4 0 false, Step.rw 1 10 0 false, Step.mv 4 3, Step.mv 5 4, Step.rw 4 5 0 false, Step.rw 3 2 0 true,
     Step.rw 5 3 0 false, Step.mv 16 24, Step.mv 15 23, Step.mv 14 22, Step.mv 13 21, Step.mv 12 20, Step.mv 11 19,
     Step.mv 10 18, Step.rw 0 24 0 false, Step.mv 10 7, Step.mv 11 8, Step.mv 12 9, Step.mv 13 10, Step.rw 9 12 1 false,
     Step.mv 21 22, Step.mv 20 21, Step.mv 19 20, Step.mv 18 19, Step.mv 17 18, Step.mv 16 17, Step.mv 15 16,
     Step.rw 0 21 0 false, Step.rw 12 2 0 false, Step.mv 5 4, Step.mv 7 5, Step.mv 10 6, Step.mv 11 7, Step.mv 12 8,
     Step.mv 13 9, Step.mv 14 10, Step.rw 2 4 0 false, Step.rw 10 8 1 false, Step.mv 17 19, Step.mv 16 18, Step.mv 15 17,
     Step.mv 14 16, Step.rw 0 17 0 false, Step.mv 7 4, Step.mv 8 5, Step.rw 1 4 1 false, Step.mv 7 6, Step.mv 8 7,
     Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.mv 12 11, Step.rw 4 12 0 false, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.rw 4 11 0 false, Step.rw 3 10 0 false, Step.mv 12 11, Step.mv 13 12,
     Step.rw 3 9 0 false, Step.mv 11 10, Step.mv 12 11, Step.rw 3 8 0 false, Step.mv 10 9, Step.mv 11 10,
     Step.rw 4 8 0 true, Step.mv 8 5, Step.rw 4 9 0 true, Step.mv 9 6, Step.rw 2 11 0 true, Step.rw 4 10 0 true,
     Step.mv 10 7, Step.mv 18 8, Step.rw 8 4 0 true, Step.mv 2 0, Step.mv 8 4, Step.rw 0 18 0 true, Step.mv 25 8,
     Step.mv 25 9, Step.mv 25 10, Step.mv 25 11, Step.mv 25 12, Step.mv 25 13, Step.mv 25 14, Step.rw 6 1 0 true,
     Step.rw 1 14 1 true, Step.mv 16 15, Step.rw 7 11 1 true, Step.rw 0 16 0 true, Step.mv 23 14, Step.mv 23 15,
     Step.mv 23 16, Step.mv 23 17, Step.mv 23 18, Step.mv 23 19, Step.mv 23 20, Step.rw 11 11 1 true, Step.mv 20 15,
     Step.rw 7 11 1 true, Step.rw 0 20 0 true, Step.mv 27 17, Step.rw 8 13 1 true, Step.rw 1 11 0 true,
     Step.mv 28 12, Step.rw 7 8 0 true, Step.rw 0 28 0 true, Step.mv 35 11, Step.mv 35 12, Step.mv 35 13, Step.mv 35 14,
     Step.mv 35 15, Step.mv 35 16, Step.mv 35 17, Step.rw 11 8 0 true, Step.mv 17 13, Step.mv 18 14, Step.mv 19 15,
     Step.mv 20 16, Step.rw 14 3 0 true, Step.mv 13 9, Step.mv 14 11, Step.mv 15 13, Step.mv 16 14, Step.mv 17 15,
     Step.mv 24 16, Step.mv 24 17, Step.mv 24 18, Step.mv 24 19, Step.mv 24 20, Step.mv 24 21, Step.mv 24 22,
     Step.rw 13 6 0 true, Step.rw 0 12 0 true, Step.mv 19 9, Step.mv 19 10, Step.mv 19 11, Step.mv 19 12, Step.mv 19 13,
     Step.mv 19 14, Step.mv 19 15, Step.rw 11 6 1 true, Step.rw 2 6 0 true, Step.rw 1 8 0 true, Step.mv 3 2,
     Step.mv 12 6, Step.mv 13 8, Step.rw 15 3 0 true, Step.mv 3 2, Step.mv 4 3, Step.mv 5 4, Step.rw 4 1 0 true, Step.mv 1 0,
     Step.mv 18 15, Step.rw 8 11 1 true, Step.rw 2 13 1 true, Step.rw 0 22 0 true, Step.mv 29 16,
     Step.rw 8 12 1 true, Step.rw 1 10 0 true, Step.mv 5 3, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.mv 15 10,
     Step.mv 16 11, Step.rw 17 2 0 true, Step.mv 2 1, Step.mv 5 4, Step.mv 6 5, Step.rw 2 8 0 true, Step.mv 13 8,
     Step.mv 14 10, Step.mv 15 12, Step.mv 16 13, Step.rw 12 6 0 true, Step.rw 4 9 0 true, Step.mv 9 6,
     Step.rw 4 10 0 true, Step.mv 10 7, Step.rw 1 8 0 true, Step.mv 2 0, Step.mv 10 5, Step.mv 11 7, Step.mv 24 11,
     Step.mv 24 12, Step.mv 24 13, Step.mv 24 14, Step.mv 24 15, Step.mv 24 16, Step.mv 24 17, Step.rw 16 1 0 true,
     Step.mv 1 0, Step.mv 2 1, Step.mv 3 2, Step.mv 6 5])
    (by decide +kernel)

end QCert.SelingerClifford
