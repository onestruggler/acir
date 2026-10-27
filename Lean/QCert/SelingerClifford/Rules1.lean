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
    (steps := [.rw 0 0 0 true, .rw 1 1 0 true, .rw 0 2 1 true, .rw 0 2 0 true, .mv 4 3, .rw 1 4 0 true,
     .rw 0 5 1 true, .rw 0 5 0 true, .mv 7 6, .rw 1 7 0 true, .mv 6 5, .mv 10 9, .mv 13 12])
    (by decide +kernel)

/-- Equation 3.3 (supplement: `[H 0 A 1 0]·ω^0 = [A 2 0]·ω^0`). -/
theorem rule_3_3 :
    Holds 1 ([.H 0] ++ bA 1 0)
      (bA 2 0) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.4 (supplement: `[H 0 A 2 0]·ω^0 = [A 1 0]·ω^0`). -/
theorem rule_3_4 :
    Holds 1 ([.H 0] ++ bA 2 0)
      (bA 1 0) :=
  Holds.of_derives (db_ok_cons hC2 db_ok_nil)
    (steps := [.rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.5 (supplement: `[H 0 A 3 0]·ω^0 = [A 3 0 X 0 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_5 :
    Holds 1 ([.H 0] ++ bA 3 0)
      (bA 3 0 ++ bX 0 ++ [.S 0, .S 0, .S 0, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL6 db_ok_nil))))
    (steps := [.rw 1 0 0 false, .rw 2 2 0 true, .rw 0 6 0 true, .mv 13 3, .mv 13 4, .mv 13 5, .mv 13 6,
     .mv 13 7, .mv 13 8, .mv 13 9, .rw 3 0 0 true, .rw 1 2 0 true])
    (by decide +kernel)

/-- Equation 3.6 (supplement: `[S 0 A 1 0]·ω^0 = [A 1 0 S 0]·ω^0`). -/
theorem rule_3_6 :
    Holds 1 ([.S 0] ++ bA 1 0)
      (bA 1 0 ++ [.S 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.7 (supplement: `[S 0 A 2 0]·ω^0 = [A 3 0 X 0 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_7 :
    Holds 1 ([.S 0] ++ bA 2 0)
      (bA 3 0 ++ bX 0 ++ [.S 0, .S 0, .S 0, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL6 db_ok_nil))))
    (steps := [.rw 2 2 0 true, .rw 0 6 0 true, .mv 13 3, .mv 13 4, .mv 13 5, .mv 13 6, .mv 13 7, .mv 13 8,
     .mv 13 9, .rw 3 0 0 true, .rw 1 2 0 true])
    (by decide +kernel)

/-- Equation 3.8 (supplement: `[S 0 A 3 0]·ω^0 = [A 2 0 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_8 :
    Holds 1 ([.S 0] ++ bA 3 0)
      (bA 2 0 ++ [.S 0, .S 0, .S 0, .om]) :=
  Holds.of_derives (db_ok_cons hL5 db_ok_nil)
    (steps := [.rw 0 0 0 false])
    (by decide +kernel)

/-- Equation 3.9 (supplement: `[ZZ 0 1 A 1 0]·ω^0 = [A 1 0 ZZ 0 1]·ω^0`). -/
theorem rule_3_9 :
    Holds 2 ([.CZ 0] ++ bA 1 1)
      (bA 1 1 ++ [.CZ 0]) :=
  Holds.of_derives (db_ok_nil)
    (steps := [])
    (by decide +kernel)

/-- Equation 3.10 (supplement: `[ZZ 0 1 A 2 0]·ω^0 = [A 1 1 B 2 0 1 ZZ 0 1 H 1]·ω^0`). -/
theorem rule_3_10 :
    Holds 2 ([.CZ 0] ++ bA 2 1)
      (bA 1 0 ++ bB 2 0 ++ [.CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 db_ok_nil))
    (steps := [.rw 0 1 0 true, .mv 3 2, .rw 1 3 0 true, .mv 2 1])
    (by decide +kernel)

/-- Equation 3.11 (supplement: `[ZZ 0 1 A 3 0]·ω^0 = [A 1 1 B 3 0 1 H 1 S 1 H 1 ZZ 0 1 S 0 S 0 S 0 H 1]·ω^0`). -/
theorem rule_3_11 :
    Holds 2 ([.CZ 0] ++ bA 3 1)
      (bA 1 0 ++ bB 3 0 ++ [.H 0, .S 0, .H 0, .CZ 0, .S 1, .S 1, .S 1, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hL5 (db_ok_cons hL9 (db_ok_cons hL14 (db_ok_cons hL17 db_ok_nil))))))))))
    (steps := [.rw 2 2 1 true, .rw 0 8 0 true, .mv 15 5, .rw 6 1 1 true, .rw 1 1 0 true, .mv 3 2, .mv 4 3,
     .rw 3 4 0 true, .mv 18 12, .mv 18 13, .mv 18 14, .mv 18 15, .mv 18 16, .mv 18 17,
     .rw 7 7 1 true, .rw 2 6 0 true, .rw 1 5 1 true, .mv 13 8, .mv 14 10, .mv 15 12,
     .mv 16 13, .rw 8 6 0 true, .rw 5 9 0 true, .mv 9 5, .rw 5 10 0 true, .mv 10 6,
     .rw 1 7 0 true, .rw 2 8 0 true, .mv 22 11, .rw 6 7 0 true, .mv 13 10, .mv 14 11,
     .mv 15 12, .mv 16 13, .rw 9 0 0 true, .mv 3 2, .rw 4 1 0 true, .mv 4 3, .mv 11 10,
     .mv 12 11, .mv 13 12])
    (by decide +kernel)

/-- Equation 3.12 (supplement: `[ZZ 0 1 A 1 1 B 1 0 1]·ω^0 = [A 1 1 B 1 0 1 H 1 ZZ 0 1 H 1]·ω^0`). -/
theorem rule_3_12 :
    Holds 2 ([.CZ 0] ++ bA 1 0 ++ bB 1 0)
      (bA 1 0 ++ bB 1 0 ++ [.H 0, .CZ 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL18 (db_ok_cons hM18 db_ok_nil)))
    (steps := [.mv 7 6, .rw 0 9 0 true, .rw 1 2 0 true, .mv 2 1, .mv 5 4, .mv 8 7, .rw 2 0 0 true, .mv 3 2,
     .mv 6 5, .mv 6 5])
    (by decide +kernel)

/-- Equation 3.13 (supplement: `[ZZ 0 1 A 1 1 B 2 0 1]·ω^0 = [A 2 0 H 1 ZZ 0 1]·ω^0`). -/
theorem rule_3_13 :
    Holds 2 ([.CZ 0] ++ bA 1 0 ++ bB 2 0)
      (bA 2 1 ++ [.H 0, .CZ 0]) :=
  Holds.of_derives (db_ok_cons hC5 db_ok_nil)
    (steps := [.mv 3 2, .rw 0 0 0 false, .mv 1 0])
    (by decide +kernel)

/-- Equation 3.14 (supplement: `[ZZ 0 1 A 1 1 B 3 0 1]·ω^0 = [A 3 0 H 1 ZZ 0 1 S 0 S 1 H 1 S 1]·ω^7`). -/
theorem rule_3_14 :
    Holds 2 ([.CZ 0] ++ bA 1 0 ++ bB 3 0)
      (bA 3 1 ++ [.H 0, .CZ 0, .S 1, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL8 (db_ok_cons hL9 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hM14 db_ok_nil))))))))))))))
    (steps := [.mv 5 4, .rw 2 2 0 false, .mv 4 3, .rw 4 0 0 false, .mv 13 17, .mv 12 16, .mv 11 15,
     .mv 10 14, .mv 9 13, .mv 8 12, .mv 7 11, .mv 7 4, .rw 11 7 0 false, .mv 10 9, .mv 12 10,
     .rw 1 6 1 false, .rw 2 5 0 false, .mv 7 6, .mv 8 7, .rw 3 2 0 true, .mv 2 0,
     .rw 5 3 0 false, .mv 16 23, .mv 15 22, .mv 14 21, .mv 13 20, .mv 12 19, .mv 11 18,
     .mv 10 17, .rw 0 23 0 false, .mv 3 1, .mv 4 2, .mv 7 6, .mv 8 7, .mv 9 8, .mv 10 9,
     .mv 11 10, .rw 8 11 1 false, .rw 0 19 0 false, .mv 3 0, .mv 4 1, .rw 13 2 0 false,
     .mv 2 0, .mv 6 5, .mv 8 6, .mv 9 7, .mv 10 8, .mv 11 9, .mv 12 10, .mv 13 11, .mv 14 12,
     .rw 7 6 0 false, .mv 10 21, .rw 6 4 0 false, .mv 8 21, .rw 10 4 0 false, .mv 13 23,
     .mv 12 22, .mv 11 21, .mv 10 20, .mv 9 19, .mv 8 18, .mv 7 17, .rw 0 20 0 false,
     .rw 6 4 0 false, .mv 8 17, .rw 8 9 1 false, .mv 18 20, .mv 17 19, .mv 16 18, .mv 15 17,
     .rw 0 17 0 false, .rw 9 9 1 false, .mv 19 20, .mv 18 19, .mv 17 18, .mv 16 17,
     .mv 15 16, .mv 14 15, .mv 9 4, .mv 10 6, .mv 11 8, .mv 12 9, .mv 13 10, .rw 0 21 0 true,
     .mv 28 11, .mv 28 12, .mv 28 13, .mv 28 14, .mv 28 15, .mv 28 16, .mv 28 17,
     .rw 12 1 0 true, .mv 1 0, .mv 2 1, .mv 3 2, .mv 8 5])
    (by decide +kernel)

/-- Equation 3.15 (supplement: `[ZZ 0 1 A 1 1 B 4 0 1]·ω^0 = [A 1 1 B 4 0 1 H 1 ZZ 0 1 S 1 S 1 H 1]·ω^0`). -/
theorem rule_3_15 :
    Holds 2 ([.CZ 0] ++ bA 1 0 ++ bB 4 0)
      (bA 1 0 ++ bB 4 0 ++ [.H 0, .CZ 0, .S 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL7 (db_ok_cons hL10 (db_ok_cons hL16 (db_ok_cons hM15 db_ok_nil))))))))))))
    (steps := [.mv 4 3, .rw 3 0 0 false, .mv 13 16, .mv 12 15, .mv 11 14, .mv 10 13, .mv 9 12, .mv 8 11,
     .mv 7 10, .mv 7 4, .rw 6 5 1 false, .mv 9 10, .rw 0 10 0 false, .rw 1 8 0 false,
     .rw 1 7 0 false, .rw 1 6 0 false, .rw 2 2 0 true, .mv 2 0, .rw 10 1 0 false, .mv 1 0,
     .rw 2 1 0 false, .rw 0 12 0 true, .mv 19 9, .mv 19 10, .mv 19 11, .mv 19 12, .mv 19 13,
     .mv 19 14, .mv 19 15, .rw 9 6 0 true, .mv 16 10, .rw 5 6 0 true, .rw 0 16 0 true,
     .mv 23 12, .rw 6 8 0 true, .mv 22 10, .mv 22 11, .rw 8 6 0 true, .mv 4 2, .mv 15 7,
     .mv 16 9, .rw 0 23 0 true, .mv 30 13, .mv 30 14, .mv 30 15, .mv 30 16, .mv 30 17,
     .mv 30 18, .mv 30 19, .rw 11 3 0 true, .mv 3 2, .mv 4 3, .mv 5 4, .rw 0 18 0 true,
     .mv 25 11, .mv 25 12, .mv 25 13, .mv 25 14, .mv 25 15, .mv 25 16, .mv 25 17,
     .rw 7 8 0 true, .mv 5 3, .mv 13 7, .mv 20 11, .mv 20 12, .mv 20 13, .mv 20 14,
     .mv 20 15, .mv 20 16, .mv 20 17, .rw 4 4 0 true, .mv 3 2])
    (by decide +kernel)

/-- Equation 3.16 (supplement: `[ZZ 0 1 A 2 1 B 1 0 1]·ω^0 = [A 2 1 B 4 0 1]·ω^0`). -/
theorem rule_3_16 :
    Holds 2 ([.CZ 0] ++ bA 2 0 ++ bB 1 0)
      (bA 2 0 ++ bB 4 0) :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 db_ok_nil))
    (steps := [.mv 8 7, .rw 0 1 0 false, .rw 1 0 0 false, .mv 4 3])
    (by decide +kernel)

/-- Equation 3.17 (supplement: `[ZZ 0 1 A 2 1 B 2 0 1]·ω^0 = [A 3 1 B 3 0 1 H 1 ZZ 0 1 S 0 S 1 S 1 H 1 S 1]·ω^6`). -/
theorem rule_3_17 :
    Holds 2 ([.CZ 0] ++ bA 2 0 ++ bB 2 0)
      (bA 3 0 ++ bB 3 0 ++ [.H 0, .CZ 0, .S 1, .S 0, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))))))))
    (steps := [.mv 4 3, .rw 5 0 0 false, .mv 13 16, .mv 12 15, .mv 11 14, .mv 10 13, .mv 9 12, .mv 8 11,
     .mv 7 10, .mv 4 3, .mv 5 4, .mv 6 5, .mv 7 6, .rw 7 3 0 false, .mv 7 10,
     .rw 0 10 0 false, .mv 7 6, .mv 8 7, .rw 4 8 0 false, .mv 6 5, .mv 7 6, .rw 4 7 0 false,
     .mv 5 4, .mv 6 5, .rw 4 6 0 false, .rw 1 10 1 true, .rw 2 11 1 true, .rw 1 13 1 true,
     .mv 10 7, .mv 11 9, .mv 12 11, .mv 13 12, .rw 10 5 0 true, .rw 4 8 0 true, .mv 8 4,
     .rw 2 10 0 true, .rw 4 9 0 true, .mv 9 5, .rw 4 10 0 true, .mv 10 6, .rw 0 18 0 true,
     .mv 25 7, .rw 7 3 0 true, .mv 7 3, .mv 24 7, .mv 24 8, .mv 24 9, .mv 24 10, .mv 24 11,
     .mv 24 12, .mv 24 13, .rw 5 0 0 true, .mv 4 3, .rw 3 2 0 true, .rw 1 10 0 true,
     .rw 2 11 0 true, .rw 0 20 0 true, .mv 27 14, .rw 7 10 0 true, .mv 16 13, .mv 17 14,
     .mv 18 15, .mv 19 16, .rw 11 3 0 true, .rw 2 12 1 true, .mv 12 9, .rw 3 8 0 true,
     .mv 22 13, .mv 22 14, .mv 22 15, .mv 22 16, .mv 22 17, .mv 22 18, .mv 22 19,
     .rw 9 10 0 true, .rw 0 20 0 true, .mv 27 14, .rw 6 10 0 true, .mv 26 16,
     .rw 7 12 0 true, .mv 6 5, .mv 7 6, .mv 8 7, .mv 17 11, .mv 18 13, .rw 12 8 0 true,
     .mv 8 5, .mv 9 6, .mv 10 7, .rw 4 11 0 true, .mv 11 8, .rw 2 13 0 true, .rw 4 12 0 true,
     .mv 12 9, .rw 4 13 0 true, .mv 13 10, .rw 0 26 0 true, .mv 33 14, .mv 33 15, .mv 33 16,
     .mv 33 17, .mv 33 18, .mv 33 19, .mv 33 20, .rw 8 11 1 true, .rw 1 14 1 true, .mv 30 11,
     .rw 7 7 0 true, .mv 11 10, .mv 12 11, .mv 13 12, .mv 14 13, .rw 11 0 0 true,
     .rw 0 22 0 true, .mv 29 10, .mv 29 11, .mv 29 12, .mv 29 13, .mv 29 14, .mv 29 15,
     .mv 29 16, .rw 9 7 1 true, .rw 2 7 0 true, .rw 1 9 0 true, .mv 3 2, .mv 4 3, .mv 13 7,
     .mv 14 9, .rw 12 4 0 true, .mv 4 2, .mv 5 3, .mv 6 4, .mv 5 2, .rw 3 1 0 true,
     .rw 4 2 0 true, .mv 2 0, .mv 28 16, .rw 7 12 1 true, .rw 2 14 1 true, .mv 31 17,
     .rw 7 13 1 true, .rw 1 11 0 true, .mv 6 4, .mv 13 8, .mv 14 9, .mv 15 10, .mv 16 11,
     .mv 17 12, .rw 14 3 0 true, .mv 3 1, .mv 6 5, .mv 7 6, .rw 3 3 0 false, .mv 5 4,
     .mv 6 5, .rw 2 9 0 true, .mv 14 9, .mv 15 11, .mv 16 13, .mv 17 14, .rw 10 7 0 true,
     .rw 4 10 0 true, .mv 10 6, .rw 4 11 0 true, .mv 11 7, .mv 8 4, .rw 3 3 0 true,
     .rw 1 9 0 true, .mv 2 0, .mv 3 1, .mv 11 6, .mv 12 8, .rw 0 27 0 true, .mv 34 12,
     .mv 34 13, .mv 34 14, .mv 34 15, .mv 34 16, .mv 34 17, .mv 34 18, .rw 13 2 0 true,
     .mv 2 0, .mv 3 1, .mv 4 2, .mv 7 6, .mv 15 11])
    (by decide +kernel)

/-- Equation 3.18 (supplement: `[ZZ 0 1 A 2 1 B 3 0 1]·ω^0 = [A 3 1 B 2 0 1 X 0 H 1 ZZ 0 1 S 0 S 0 S 0]·ω^1`). -/
theorem rule_3_18 :
    Holds 2 ([.CZ 0] ++ bA 2 0 ++ bB 3 0)
      (bA 3 0 ++ bB 2 0 ++ bX 1 ++ [.H 0, .CZ 0, .S 1, .S 1, .S 1, .om]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hL14 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil)))))))))
    (steps := [.mv 6 5, .rw 3 3 0 false, .mv 5 4, .rw 2 8 1 true, .rw 3 7 0 true, .rw 2 5 1 true,
     .rw 2 5 0 true, .rw 1 7 0 true, .mv 2 1, .mv 11 5, .mv 12 7, .rw 6 2 0 true, .mv 2 1,
     .mv 3 2, .mv 4 3, .rw 4 0 0 true, .rw 1 9 0 true, .mv 4 2, .mv 11 6, .mv 12 7, .mv 13 8,
     .mv 14 9, .mv 15 10, .rw 8 1 0 true, .mv 4 3, .mv 5 4, .rw 1 8 1 true, .rw 2 9 1 true,
     .rw 1 11 1 true, .rw 2 7 0 true, .mv 12 7, .mv 13 9, .mv 14 11, .mv 15 12,
     .rw 5 5 0 true, .rw 4 8 0 true, .mv 8 5, .rw 4 9 0 true, .mv 9 6, .rw 1 7 0 true,
     .mv 9 4, .mv 10 6, .rw 0 22 0 true, .mv 29 10, .mv 29 11, .mv 29 12, .mv 29 13,
     .mv 29 14, .mv 29 15, .mv 29 16, .rw 7 0 0 true, .mv 5 4, .mv 8 7, .mv 9 8, .mv 10 9,
     .mv 11 10])
    (by decide +kernel)

/-- Equation 3.19 (supplement: `[ZZ 0 1 A 2 1 B 4 0 1]·ω^0 = [A 2 1 B 1 0 1]·ω^0`). -/
theorem rule_3_19 :
    Holds 2 ([.CZ 0] ++ bA 2 0 ++ bB 4 0)
      (bA 2 0 ++ bB 1 0) :=
  Holds.of_derives (db_ok_cons hC2 db_ok_nil)
    (steps := [.mv 5 4, .rw 0 0 0 true, .mv 7 6])
    (by decide +kernel)

/-- Equation 3.20 (supplement: `[ZZ 0 1 A 3 1 B 1 0 1]·ω^0 = [A 3 1 B 4 0 1 H 1 ZZ 0 1 S 1 H 1]·ω^0`). -/
theorem rule_3_20 :
    Holds 2 ([.CZ 0] ++ bA 3 0 ++ bB 1 0)
      (bA 3 0 ++ bB 4 0 ++ [.H 0, .CZ 0, .S 0, .H 0]) :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL8 (db_ok_cons hL10 (db_ok_cons hL14 (db_ok_cons hL15 (db_ok_cons hL17 (db_ok_cons hM14 (db_ok_cons hM15 (db_ok_cons hM17 db_ok_nil))))))))))))))))))
    (steps := [.mv 10 9, .rw 1 3 0 false, .rw 4 2 0 false, .rw 6 0 0 false, .mv 13 20, .mv 12 19, .mv 11 18,
     .mv 10 17, .mv 9 16, .mv 8 15, .mv 7 14, .mv 4 3, .mv 5 4, .mv 6 5, .mv 7 6, .mv 8 7,
     .mv 8 5, .mv 9 6, .rw 15 7 0 false, .mv 7 5, .mv 11 10, .mv 13 11, .mv 14 12, .mv 15 13,
     .rw 1 4 0 false, .rw 1 10 0 false, .mv 4 3, .mv 5 4, .rw 4 5 0 false, .rw 3 2 0 true,
     .rw 5 3 0 false, .mv 16 24, .mv 15 23, .mv 14 22, .mv 13 21, .mv 12 20, .mv 11 19,
     .mv 10 18, .rw 0 24 0 false, .mv 10 7, .mv 11 8, .mv 12 9, .mv 13 10, .rw 9 12 1 false,
     .mv 21 22, .mv 20 21, .mv 19 20, .mv 18 19, .mv 17 18, .mv 16 17, .mv 15 16,
     .rw 0 21 0 false, .rw 12 2 0 false, .mv 5 4, .mv 7 5, .mv 10 6, .mv 11 7, .mv 12 8,
     .mv 13 9, .mv 14 10, .rw 2 4 0 false, .rw 10 8 1 false, .mv 17 19, .mv 16 18, .mv 15 17,
     .mv 14 16, .rw 0 17 0 false, .mv 7 4, .mv 8 5, .rw 1 4 1 false, .mv 7 6, .mv 8 7,
     .mv 9 8, .mv 10 9, .mv 11 10, .mv 12 11, .rw 4 12 0 false, .mv 6 5, .mv 7 6, .mv 8 7,
     .mv 9 8, .mv 10 9, .mv 11 10, .rw 4 11 0 false, .rw 3 10 0 false, .mv 12 11, .mv 13 12,
     .rw 3 9 0 false, .mv 11 10, .mv 12 11, .rw 3 8 0 false, .mv 10 9, .mv 11 10,
     .rw 4 8 0 true, .mv 8 5, .rw 4 9 0 true, .mv 9 6, .rw 2 11 0 true, .rw 4 10 0 true,
     .mv 10 7, .mv 18 8, .rw 8 4 0 true, .mv 2 0, .mv 8 4, .rw 0 18 0 true, .mv 25 8,
     .mv 25 9, .mv 25 10, .mv 25 11, .mv 25 12, .mv 25 13, .mv 25 14, .rw 6 1 0 true,
     .rw 1 14 1 true, .mv 16 15, .rw 7 11 1 true, .rw 0 16 0 true, .mv 23 14, .mv 23 15,
     .mv 23 16, .mv 23 17, .mv 23 18, .mv 23 19, .mv 23 20, .rw 11 11 1 true, .mv 20 15,
     .rw 7 11 1 true, .rw 0 20 0 true, .mv 27 17, .rw 8 13 1 true, .rw 1 11 0 true,
     .mv 28 12, .rw 7 8 0 true, .rw 0 28 0 true, .mv 35 11, .mv 35 12, .mv 35 13, .mv 35 14,
     .mv 35 15, .mv 35 16, .mv 35 17, .rw 11 8 0 true, .mv 17 13, .mv 18 14, .mv 19 15,
     .mv 20 16, .rw 14 3 0 true, .mv 13 9, .mv 14 11, .mv 15 13, .mv 16 14, .mv 17 15,
     .mv 24 16, .mv 24 17, .mv 24 18, .mv 24 19, .mv 24 20, .mv 24 21, .mv 24 22,
     .rw 13 6 0 true, .rw 0 12 0 true, .mv 19 9, .mv 19 10, .mv 19 11, .mv 19 12, .mv 19 13,
     .mv 19 14, .mv 19 15, .rw 11 6 1 true, .rw 2 6 0 true, .rw 1 8 0 true, .mv 3 2,
     .mv 12 6, .mv 13 8, .rw 15 3 0 true, .mv 3 2, .mv 4 3, .mv 5 4, .rw 4 1 0 true, .mv 1 0,
     .mv 18 15, .rw 8 11 1 true, .rw 2 13 1 true, .rw 0 22 0 true, .mv 29 16,
     .rw 8 12 1 true, .rw 1 10 0 true, .mv 5 3, .mv 12 7, .mv 13 8, .mv 14 9, .mv 15 10,
     .mv 16 11, .rw 17 2 0 true, .mv 2 1, .mv 5 4, .mv 6 5, .rw 2 8 0 true, .mv 13 8,
     .mv 14 10, .mv 15 12, .mv 16 13, .rw 12 6 0 true, .rw 4 9 0 true, .mv 9 6,
     .rw 4 10 0 true, .mv 10 7, .rw 1 8 0 true, .mv 2 0, .mv 10 5, .mv 11 7, .mv 24 11,
     .mv 24 12, .mv 24 13, .mv 24 14, .mv 24 15, .mv 24 16, .mv 24 17, .rw 16 1 0 true,
     .mv 1 0, .mv 2 1, .mv 3 2, .mv 6 5])
    (by decide +kernel)

end QCert.SelingerClifford
