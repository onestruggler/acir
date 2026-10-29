/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): the lemmas of the supplement

Equations (4)–(10), (14)–(18), (20) and (21) of Lemmas 1.1–1.3 of the
supplement to Selinger's paper, as equations between words of letters in time
order (an equation's `·ω^k` is moved to the side where `k ≥ 0`), with their
"upside-down" versions (`M…`).  Each is derived from the relations of
Figure 8 and the lemmas before it by a checked derivation, found by a search
guided by the steps of the supplement's proof.
-/
import QCert.SelingerClifford.Axioms

namespace QCert.SelingerClifford

set_option maxRecDepth 8000

/-- (4) of Lemma 1.1: `SHSH = HSSS·ω`. -/
def eL4 : Eqn :=
  ⟨1, [.H 0, .S 0, .H 0, .S 0],
    [.S 0, .S 0, .S 0, .H 0, .om]⟩

theorem hL4 : Holds eL4.k eL4.l eL4.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC4 db_ok_nil)))
    (steps := [Step.rw 1 0 0 true, Step.rw 0 3 0 true, Step.rw 2 4 0 false])
    (by decide +kernel)

/-- (5) of Lemma 1.1: `HSHS = SSSH·ω`. -/
def eL5 : Eqn :=
  ⟨1, [.S 0, .H 0, .S 0, .H 0],
    [.H 0, .S 0, .S 0, .S 0, .om]⟩

theorem hL5 : Holds eL5.k eL5.l eL5.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL4 db_ok_nil))
    (steps := [Step.rw 0 0 0 true, Step.rw 0 0 0 true, Step.rw 0 0 0 true, Step.rw 1 5 0 false, Step.mv 9 10, Step.rw 0 0 0 false,
     Step.rw 0 0 0 false, Step.rw 0 4 0 false])
    (by decide +kernel)

/-- (6) of Lemma 1.1: `HSSSH = SHS·ω⁻¹`. -/
def eL6 : Eqn :=
  ⟨1, [.H 0, .S 0, .S 0, .S 0, .H 0],
    [.S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]⟩

theorem hL6 : Holds eL6.k eL6.l eL6.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hL4 db_ok_nil)))
    (steps := [Step.rw 0 5 0 true, Step.mv 12 5, Step.rw 2 1 0 true, Step.rw 1 0 0 false])
    (by decide +kernel)

/-- (7) of Lemma 1.1: `SHSSHS = HSSH·ω²`. -/
def eL7 : Eqn :=
  ⟨1, [.S 0, .H 0, .S 0, .S 0, .H 0, .S 0],
    [.H 0, .S 0, .S 0, .H 0, .om, .om]⟩

theorem hL7 : Holds eL7.k eL7.l eL7.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL6 db_ok_nil))))
    (steps := [Step.rw 0 6 0 true, Step.mv 13 3, Step.mv 13 4, Step.mv 13 5, Step.mv 13 6, Step.mv 13 7, Step.mv 13 8, Step.mv 13 9,
     Step.rw 3 0 0 true, Step.rw 0 9 0 true, Step.mv 16 6, Step.mv 16 7, Step.mv 16 8, Step.mv 16 9, Step.mv 16 10,
     Step.mv 16 11, Step.mv 16 12, Step.rw 3 3 0 true, Step.rw 1 7 0 false, Step.rw 2 4 0 false])
    (by decide +kernel)

/-- (8) of Lemma 1.1: `HSSHSS = SSHSSH·ω⁴`. -/
def eL8 : Eqn :=
  ⟨1, [.S 0, .S 0, .H 0, .S 0, .S 0, .H 0],
    [.H 0, .S 0, .S 0, .H 0, .S 0, .S 0, .om, .om, .om, .om]⟩

theorem hL8 : Holds eL8.k eL8.l eL8.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL7 db_ok_nil))))
    (steps := [Step.rw 0 6 0 true, Step.mv 13 4, Step.mv 13 5, Step.mv 13 6, Step.mv 13 7, Step.mv 13 8, Step.mv 13 9, Step.mv 13 10,
     Step.rw 2 1 0 true, Step.rw 1 4 0 false, Step.rw 3 0 0 false, Step.mv 5 7, Step.mv 4 6])
    (by decide +kernel)

/-- (9) of Lemma 1.1: `SSSHSSH = HSSHS·ω⁻²`. -/
def eL9 : Eqn :=
  ⟨1, [.H 0, .S 0, .S 0, .H 0, .S 0, .S 0, .S 0],
    [.S 0, .H 0, .S 0, .S 0, .H 0, .om, .om, .om, .om, .om, .om]⟩

theorem hL9 : Holds eL9.k eL9.l eL9.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hL5 db_ok_nil)))
    (steps := [Step.rw 0 7 0 true, Step.mv 14 7, Step.rw 2 3 0 true, Step.rw 2 3 0 false, Step.rw 0 7 0 false, Step.rw 0 7 0 true,
     Step.mv 14 7, Step.rw 2 3 0 true, Step.mv 13 4, Step.rw 2 0 0 true, Step.rw 1 3 0 false])
    (by decide +kernel)

/-- (10) of Lemma 1.1: `SSSHSSS = HSH·ω⁻¹`. -/
def eL10 : Eqn :=
  ⟨1, [.S 0, .S 0, .S 0, .H 0, .S 0, .S 0, .S 0],
    [.H 0, .S 0, .H 0, .om, .om, .om, .om, .om, .om, .om]⟩

theorem hL10 : Holds eL10.k eL10.l eL10.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC3 (db_ok_cons hL4 db_ok_nil)))
    (steps := [Step.rw 0 7 0 true, Step.mv 14 4, Step.rw 2 0 0 true, Step.rw 1 3 0 false])
    (by decide +kernel)

/-- (14) of Lemma 1.2. -/
def eL14 : Eqn :=
  ⟨2, [.S 1, .S 1, .H 1, .CZ 0],
    [.H 1, .CZ 0, .H 1, .S 0, .S 1, .S 0, .S 1, .H 1]⟩

theorem hL14 : Holds eL14.k eL14.l eL14.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC8 db_ok_nil))
    (steps := [Step.rw 0 0 1 true, Step.rw 1 1 0 false, Step.mv 4 2, Step.mv 5 4])
    (by decide +kernel)

/-- The upside-down version of (14) of Lemma 1.2. -/
def eM14 : Eqn :=
  ⟨2, [.S 0, .S 0, .H 0, .CZ 0],
    [.H 0, .CZ 0, .H 0, .S 1, .S 0, .S 1, .S 0, .H 0]⟩

theorem hM14 : Holds eM14.k eM14.l eM14.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC9 db_ok_nil))
    (steps := [Step.rw 0 0 0 true, Step.rw 1 1 0 false, Step.mv 4 2, Step.mv 5 4])
    (by decide +kernel)

/-- (15) of Lemma 1.2. -/
def eL15 : Eqn :=
  ⟨2, [.H 1, .S 1, .H 1, .CZ 0],
    [.S 1, .H 1, .CZ 0, .S 1, .S 0, .H 1, .S 0, .S 1, .S 1, .H 1, .om, .om, .om, .om, .om, .om,
     .om]⟩

theorem hL15 : Holds eL15.k eL15.l eL15.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC6 (db_ok_cons hL5 (db_ok_cons hL10 (db_ok_cons hL14 db_ok_nil))))))
    (steps := [Step.rw 0 4 0 true, Step.mv 11 3, Step.mv 11 4, Step.mv 11 5, Step.mv 11 6, Step.mv 11 7, Step.mv 11 8, Step.mv 11 9,
     Step.rw 4 0 1 true, Step.rw 2 6 0 false, Step.rw 2 5 0 false, Step.rw 2 4 0 false, Step.rw 5 1 0 false,
     Step.mv 5 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.rw 3 6 1 true,
     Step.mv 10 7, Step.mv 11 8, Step.rw 0 12 0 true, Step.mv 19 7, Step.rw 3 3 1 true, Step.mv 7 4, Step.mv 8 6,
     Step.rw 1 8 1 false])
    (by decide +kernel)

/-- The upside-down version of (15) of Lemma 1.2. -/
def eM15 : Eqn :=
  ⟨2, [.H 0, .S 0, .H 0, .CZ 0],
    [.S 0, .H 0, .CZ 0, .S 0, .S 1, .H 0, .S 1, .S 0, .S 0, .H 0, .om, .om, .om, .om, .om, .om,
     .om]⟩

theorem hM15 : Holds eM15.k eM15.l eM15.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC7 (db_ok_cons hL5 (db_ok_cons hL10 (db_ok_cons hM14 db_ok_nil))))))
    (steps := [Step.rw 0 4 0 true, Step.mv 11 3, Step.mv 11 4, Step.mv 11 5, Step.mv 11 6, Step.mv 11 7, Step.mv 11 8, Step.mv 11 9,
     Step.rw 4 0 0 true, Step.rw 2 6 0 false, Step.rw 2 5 0 false, Step.rw 2 4 0 false, Step.rw 5 1 0 false,
     Step.mv 5 4, Step.mv 7 5, Step.mv 8 6, Step.mv 9 7, Step.mv 10 8, Step.mv 11 9, Step.mv 12 10, Step.rw 3 6 0 true,
     Step.mv 10 7, Step.mv 11 8, Step.rw 0 12 0 true, Step.mv 19 7, Step.rw 3 3 0 true, Step.mv 7 4, Step.mv 8 6,
     Step.rw 1 8 0 false])
    (by decide +kernel)

/-- (16) of Lemma 1.2. -/
def eL16 : Eqn :=
  ⟨2, [.S 1, .H 1, .CZ 0, .H 0, .H 1, .CZ 0],
    [.H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .S 0, .H 0]⟩

theorem hL16 : Holds eL16.k eL16.l eL16.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hM14 db_ok_nil)))))))))
    (steps := [Step.mv 4 3, Step.rw 2 4 0 true, Step.rw 4 2 0 false, Step.mv 15 18, Step.mv 14 17, Step.mv 13 16, Step.mv 12 15,
     Step.mv 11 14, Step.mv 10 13, Step.mv 9 12, Step.rw 7 0 1 false, Step.mv 4 12, Step.rw 0 12 0 false,
     Step.rw 3 3 0 false, Step.mv 5 4, Step.rw 3 2 0 false, Step.mv 4 3, Step.rw 3 1 0 false, Step.mv 4 3, Step.mv 5 4,
     Step.mv 6 5, Step.mv 7 6, Step.rw 1 2 1 false, Step.rw 5 5 0 false, Step.mv 4 3, Step.rw 8 4 0 false, Step.mv 4 3,
     Step.mv 12 11, Step.rw 3 4 0 false, Step.mv 7 6, Step.mv 9 7, Step.mv 11 8, Step.rw 1 5 1 false, Step.rw 1 1 1 true,
     Step.rw 1 1 1 true, Step.mv 11 10, Step.rw 6 16 0 false, Step.rw 0 20 0 false, Step.rw 1 1 1 false,
     Step.rw 1 1 1 false, Step.rw 1 6 0 false])
    (by decide +kernel)

/-- The upside-down version of (16) of Lemma 1.2. -/
def eM16 : Eqn :=
  ⟨2, [.S 0, .H 0, .CZ 0, .H 1, .H 0, .CZ 0],
    [.H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .S 1, .H 1]⟩

theorem hM16 : Holds eM16.k eM16.l eM16.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL5 (db_ok_cons hL14 db_ok_nil)))))))))
    (steps := [Step.mv 4 3, Step.rw 2 4 0 true, Step.rw 5 2 0 false, Step.mv 15 18, Step.mv 14 17, Step.mv 13 16, Step.mv 12 15,
     Step.mv 11 14, Step.mv 10 13, Step.mv 9 12, Step.rw 7 0 0 false, Step.mv 4 12, Step.rw 0 12 0 false,
     Step.rw 3 3 0 false, Step.mv 5 4, Step.rw 3 2 0 false, Step.mv 4 3, Step.rw 3 1 0 false, Step.mv 4 3, Step.mv 5 4,
     Step.mv 6 5, Step.mv 7 6, Step.rw 1 2 0 false, Step.rw 4 5 0 false, Step.mv 4 3, Step.rw 8 4 0 false, Step.mv 4 3,
     Step.mv 12 11, Step.rw 3 4 0 false, Step.mv 7 6, Step.mv 9 7, Step.mv 11 8, Step.rw 1 5 0 false, Step.rw 1 1 0 true,
     Step.rw 1 1 0 true, Step.mv 11 10, Step.rw 6 16 1 false, Step.rw 0 20 0 false, Step.rw 1 1 0 false,
     Step.rw 1 1 0 false, Step.rw 1 6 1 false])
    (by decide +kernel)

/-- (17) of Lemma 1.2. -/
def eL17 : Eqn :=
  ⟨2, [.H 1, .CZ 0, .H 0, .S 1, .H 1, .CZ 0],
    [.CZ 0, .H 0, .S 1, .H 1, .CZ 0, .S 0, .S 0, .S 0, .H 0, .S 0, .H 1, .S 1, .S 1, .H 1]⟩

theorem hL17 : Holds eL17.k eL17.l eL17.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC8 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL7 (db_ok_cons hL15 db_ok_nil))))))))))
    (steps := [Step.mv 3 2, Step.rw 3 1 0 true, Step.mv 4 3, Step.rw 2 4 0 true, Step.rw 5 2 0 false, Step.mv 15 18, Step.mv 14 17,
     Step.mv 13 16, Step.mv 12 15, Step.mv 11 14, Step.mv 10 13, Step.mv 9 12, Step.rw 4 0 0 false, Step.mv 3 1, Step.mv 4 3,
     Step.mv 7 6, Step.rw 7 7 1 false, Step.mv 11 14, Step.rw 0 14 0 false, Step.mv 3 2, Step.mv 5 3, Step.mv 7 4,
     Step.mv 8 5, Step.mv 9 7, Step.mv 10 9, Step.rw 1 2 1 false, Step.rw 6 7 0 false, Step.mv 2 1, Step.mv 4 2, Step.mv 6 3,
     Step.mv 7 4, Step.rw 1 1 0 false, Step.mv 4 1, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.rw 9 2 0 false,
     Step.mv 18 22, Step.mv 17 21, Step.mv 16 20, Step.mv 15 19, Step.mv 14 18, Step.mv 13 17, Step.mv 12 16,
     Step.rw 0 22 0 false, Step.mv 6 5, Step.mv 8 6, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.rw 8 10 1 false,
     Step.rw 0 14 0 false])
    (by decide +kernel)

/-- The upside-down version of (17) of Lemma 1.2. -/
def eM17 : Eqn :=
  ⟨2, [.H 0, .CZ 0, .H 1, .S 0, .H 0, .CZ 0],
    [.CZ 0, .H 1, .S 0, .H 0, .CZ 0, .S 1, .S 1, .S 1, .H 1, .S 1, .H 0, .S 0, .S 0, .H 0]⟩

theorem hM17 : Holds eM17.k eM17.l eM17.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC7 (db_ok_cons hC9 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL4 (db_ok_cons hL7 (db_ok_cons hM15 db_ok_nil))))))))))
    (steps := [Step.mv 3 2, Step.rw 3 1 0 true, Step.mv 4 3, Step.rw 2 4 0 true, Step.rw 6 2 0 false, Step.mv 15 18, Step.mv 14 17,
     Step.mv 13 16, Step.mv 12 15, Step.mv 11 14, Step.mv 10 13, Step.mv 9 12, Step.rw 4 0 0 false, Step.mv 3 1, Step.mv 4 3,
     Step.mv 7 6, Step.rw 7 7 0 false, Step.mv 11 14, Step.rw 0 14 0 false, Step.mv 3 2, Step.mv 5 3, Step.mv 7 4,
     Step.mv 8 5, Step.mv 9 7, Step.mv 10 9, Step.rw 1 2 0 false, Step.rw 5 7 0 false, Step.mv 2 1, Step.mv 4 2, Step.mv 6 3,
     Step.mv 7 4, Step.rw 1 1 1 false, Step.mv 4 1, Step.mv 7 6, Step.mv 8 7, Step.mv 9 8, Step.rw 9 2 0 false,
     Step.mv 18 22, Step.mv 17 21, Step.mv 16 20, Step.mv 15 19, Step.mv 14 18, Step.mv 13 17, Step.mv 12 16,
     Step.rw 0 22 0 false, Step.mv 6 5, Step.mv 8 6, Step.mv 12 7, Step.mv 13 8, Step.mv 14 9, Step.rw 8 10 0 false,
     Step.rw 0 14 0 false])
    (by decide +kernel)

/-- (18) of Lemma 1.2. -/
def eL18 : Eqn :=
  ⟨2, [.H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0],
    [.CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0]⟩

theorem hL18 : Holds eL18.k eL18.l eL18.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL15 (db_ok_cons hL16 (db_ok_cons hL17 (db_ok_cons hM14 db_ok_nil))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.rw 3 6 0 true, Step.rw 6 4 0 false, Step.mv 17 20, Step.mv 16 19, Step.mv 15 18,
     Step.mv 14 17, Step.mv 13 16, Step.mv 12 15, Step.mv 11 14, Step.mv 3 2, Step.rw 10 3 0 false, Step.mv 19 26,
     Step.mv 18 25, Step.mv 17 24, Step.mv 16 23, Step.mv 15 22, Step.mv 14 21, Step.mv 13 20, Step.rw 0 26 0 false,
     Step.mv 8 7, Step.mv 10 9, Step.mv 13 12, Step.rw 12 0 0 false, Step.mv 2 1, Step.mv 10 5, Step.mv 11 7, Step.mv 12 9,
     Step.mv 13 11, Step.mv 14 13, Step.mv 15 14, Step.mv 17 15, Step.mv 19 16, Step.mv 21 17, Step.mv 22 18,
     Step.rw 9 13 1 false, Step.mv 18 27, Step.mv 17 26, Step.rw 0 26 0 false, Step.mv 13 12, Step.rw 1 11 1 false,
     Step.mv 19 15, Step.rw 1 14 1 false, Step.mv 9 8, Step.mv 12 9, Step.mv 13 10, Step.rw 2 7 1 false,
     Step.rw 2 10 0 false, Step.rw 4 10 0 false, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.rw 5 4 0 true,
     Step.rw 5 5 0 true, Step.rw 5 6 0 true, Step.mv 2 1, Step.mv 4 2, Step.mv 5 3, Step.mv 6 4, Step.mv 9 8,
     Step.rw 11 5 0 false, Step.mv 14 13, Step.rw 1 12 0 false, Step.mv 5 1, Step.mv 8 7, Step.mv 12 11,
     Step.rw 5 12 0 false, Step.rw 4 11 0 false, Step.rw 7 9 0 false, Step.mv 22 24, Step.mv 21 23, Step.mv 20 22,
     Step.mv 19 21, Step.mv 18 20, Step.mv 17 19, Step.mv 16 18, Step.mv 16 14, Step.rw 5 5 0 false, Step.mv 7 6,
     Step.rw 5 4 0 false, Step.mv 6 5, Step.rw 5 3 0 false, Step.mv 5 4, Step.rw 8 7 0 false, Step.mv 11 18,
     Step.rw 0 18 0 false, Step.mv 13 12, Step.mv 15 14, Step.rw 5 11 0 true, Step.rw 2 8 0 false, Step.mv 11 10,
     Step.rw 13 5 0 false, Step.mv 15 13, Step.rw 1 12 0 false, Step.mv 10 9, Step.mv 12 10, Step.mv 13 11,
     Step.rw 2 8 1 false, Step.rw 2 8 0 false, Step.mv 2 1, Step.mv 5 4])
    (by decide +kernel)

/-- The upside-down version of (18) of Lemma 1.2. -/
def eM18 : Eqn :=
  ⟨2, [.H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 0],
    [.CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1]⟩

theorem hM18 : Holds eM18.k eM18.l eM18.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC6 (db_ok_cons hC7 (db_ok_cons hC10 (db_ok_cons hC11 (db_ok_cons hL5 (db_ok_cons hL7 (db_ok_cons hL14 (db_ok_cons hM15 (db_ok_cons hM16 (db_ok_cons hM17 db_ok_nil))))))))))))))
    (steps := [Step.mv 3 2, Step.mv 6 5, Step.rw 3 6 0 true, Step.rw 7 4 0 false, Step.mv 17 20, Step.mv 16 19, Step.mv 15 18,
     Step.mv 14 17, Step.mv 13 16, Step.mv 12 15, Step.mv 11 14, Step.mv 3 2, Step.rw 11 3 0 false, Step.mv 19 26,
     Step.mv 18 25, Step.mv 17 24, Step.mv 16 23, Step.mv 15 22, Step.mv 14 21, Step.mv 13 20, Step.rw 0 26 0 false,
     Step.mv 8 7, Step.mv 10 9, Step.mv 13 12, Step.rw 13 0 0 false, Step.mv 2 1, Step.mv 10 5, Step.mv 11 7, Step.mv 12 9,
     Step.mv 13 11, Step.mv 14 13, Step.mv 15 14, Step.mv 17 15, Step.mv 19 16, Step.mv 21 17, Step.mv 22 18,
     Step.rw 9 13 0 false, Step.mv 18 27, Step.mv 17 26, Step.rw 0 26 0 false, Step.mv 13 12, Step.rw 1 11 0 false,
     Step.mv 19 15, Step.rw 1 14 0 false, Step.mv 9 8, Step.mv 12 9, Step.mv 13 10, Step.rw 2 7 0 false,
     Step.rw 2 10 1 false, Step.rw 5 10 0 false, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7, Step.rw 4 4 0 true,
     Step.rw 4 5 0 true, Step.rw 4 6 0 true, Step.mv 2 1, Step.mv 4 2, Step.mv 5 3, Step.mv 6 4, Step.mv 9 8,
     Step.rw 12 5 0 false, Step.mv 14 13, Step.rw 1 12 1 false, Step.mv 5 1, Step.mv 8 7, Step.mv 12 11,
     Step.rw 4 12 0 false, Step.rw 5 11 0 false, Step.rw 6 9 0 false, Step.mv 22 24, Step.mv 21 23, Step.mv 20 22,
     Step.mv 19 21, Step.mv 18 20, Step.mv 17 19, Step.mv 16 18, Step.mv 16 14, Step.rw 4 5 0 false, Step.mv 7 6,
     Step.rw 4 4 0 false, Step.mv 6 5, Step.rw 4 3 0 false, Step.mv 5 4, Step.rw 8 7 1 false, Step.mv 11 18,
     Step.rw 0 18 0 false, Step.mv 13 12, Step.mv 15 14, Step.rw 4 11 0 true, Step.rw 2 8 1 false, Step.mv 11 10,
     Step.rw 10 5 0 false, Step.mv 15 13, Step.rw 1 12 1 false, Step.mv 10 9, Step.mv 12 10, Step.mv 13 11,
     Step.rw 2 8 0 false, Step.rw 2 8 1 false, Step.mv 2 1, Step.mv 5 4])
    (by decide +kernel)

/-- (20) of Lemma 1.3. -/
def eL20 : Eqn :=
  ⟨3, [.CZ 0, .H 1, .H 0, .CZ 1, .H 2, .H 1, .CZ 1, .H 2, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .CZ 1],
    [.H 1, .H 0, .CZ 1, .H 2, .H 1, .CZ 1, .H 2, .CZ 0, .H 1, .H 0, .CZ 0, .H 1]⟩

theorem hL20 : Holds eL20.k eL20.l eL20.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC13 db_ok_nil)))
    (steps := [Step.rw 0 0 0 true, Step.rw 0 0 1 true, Step.mv 1 2, Step.mv 3 2, Step.rw 1 2 1 true, Step.mv 3 4, Step.rw 0 4 1 true,
     Step.rw 0 4 2 true, Step.mv 5 6, Step.rw 1 6 1 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.rw 2 6 0 false, Step.mv 20 19, Step.rw 1 18 0 false, Step.mv 18 15,
     Step.rw 0 14 2 false, Step.rw 0 16 1 false, Step.rw 0 15 0 false, Step.rw 1 14 0 false,
     Step.rw 0 13 1 false, Step.rw 1 12 1 false, Step.mv 11 6, Step.mv 9 8])
    (by decide +kernel)

/-- The upside-down version of (20) of Lemma 1.3. -/
def eM20 : Eqn :=
  ⟨3, [.CZ 1, .H 1, .H 2, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .CZ 1, .H 1, .H 2, .CZ 1, .H 1, .CZ 0],
    [.H 1, .H 2, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .CZ 1, .H 1, .H 2, .CZ 1, .H 1]⟩

theorem hM20 : Holds eM20.k eM20.l eM20.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC5 (db_ok_cons hC13 db_ok_nil)))
    (steps := [Step.rw 0 0 2 true, Step.rw 0 0 1 true, Step.mv 1 2, Step.mv 3 2, Step.rw 1 2 0 true, Step.mv 3 4, Step.rw 0 4 1 true,
     Step.rw 0 4 0 true, Step.mv 5 6, Step.rw 1 6 0 true, Step.mv 4 3, Step.mv 5 4, Step.mv 6 5, Step.mv 7 6, Step.mv 8 7,
     Step.mv 9 8, Step.mv 10 9, Step.mv 11 10, Step.rw 2 6 0 true, Step.mv 20 19, Step.rw 1 18 1 false, Step.mv 18 15,
     Step.rw 0 14 0 false, Step.rw 0 16 1 false, Step.rw 0 15 2 false, Step.rw 1 14 1 false,
     Step.rw 0 13 1 false, Step.rw 1 12 0 false, Step.mv 11 6, Step.mv 9 8])
    (by decide +kernel)

/-- (21) of Lemma 1.3. -/
def eL21 : Eqn :=
  ⟨3, [.CZ 0, .H 1, .H 0, .CZ 1, .H 1, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 1, .S 1, .H 1,
       .CZ 0],
    [.H 1, .H 0, .CZ 0, .CZ 1, .H 0, .S 1, .S 0, .H 1, .S 0, .S 0]⟩

theorem hL21 : Holds eL21.k eL21.l eL21.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC10 (db_ok_cons hC12 (db_ok_cons hC15 (db_ok_cons hL5 (db_ok_cons hL18 db_ok_nil)))))))))
    (steps := [Step.rw 1 15 1 true, Step.rw 2 16 1 true, Step.rw 2 16 0 true, Step.mv 19 22, Step.mv 18 20, Step.mv 17 18,
     Step.mv 17 16, Step.mv 19 17, Step.mv 21 18, Step.rw 0 25 0 true, Step.mv 32 19, Step.rw 7 15 1 true, Step.mv 19 15,
     Step.mv 23 21, Step.mv 24 23, Step.mv 31 19, Step.mv 31 20, Step.mv 31 21, Step.mv 31 22, Step.mv 31 23, Step.mv 31 24,
     Step.mv 31 25, Step.rw 4 12 0 true, Step.rw 5 11 0 true, Step.mv 7 6, Step.mv 10 9, Step.rw 8 4 0 false,
     Step.mv 6 5, Step.mv 9 8, Step.mv 12 11, Step.mv 13 12, Step.rw 5 10 0 false, Step.mv 17 16, Step.mv 19 17,
     Step.rw 1 16 0 true, Step.mv 17 18, Step.mv 18 17, Step.mv 20 18, Step.mv 21 20, Step.rw 3 17 1 true, Step.mv 18 19,
     Step.rw 1 0 0 true, Step.rw 1 0 1 true, Step.mv 1 2, Step.rw 3 2 0 true, Step.mv 5 4, Step.mv 8 7, Step.mv 12 11,
     Step.mv 15 14, Step.mv 19 18, Step.mv 25 24, Step.mv 27 26, Step.mv 29 28, Step.rw 6 3 0 false])
    (by decide +kernel)

/-- The upside-down version of (21) of Lemma 1.3. -/
def eM21 : Eqn :=
  ⟨3, [.CZ 1, .H 1, .H 2, .CZ 0, .H 1, .CZ 1, .H 1, .H 2, .CZ 1, .H 1, .H 2, .CZ 0, .S 1, .H 1,
       .CZ 1],
    [.H 1, .H 2, .CZ 1, .CZ 0, .H 2, .S 1, .S 2, .H 1, .S 2, .S 2]⟩

theorem hM21 : Holds eM21.k eM21.l eM21.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hC5 (db_ok_cons hC11 (db_ok_cons hC12 (db_ok_cons hC14 (db_ok_cons hL5 (db_ok_cons hM18 db_ok_nil)))))))))
    (steps := [Step.rw 1 15 1 true, Step.rw 2 16 1 true, Step.rw 2 16 2 true, Step.mv 19 22, Step.mv 18 20, Step.mv 17 18,
     Step.mv 17 16, Step.mv 19 17, Step.mv 21 18, Step.rw 0 25 0 true, Step.mv 32 19, Step.rw 7 15 1 true, Step.mv 19 15,
     Step.mv 23 21, Step.mv 24 23, Step.mv 31 19, Step.mv 31 20, Step.mv 31 21, Step.mv 31 22, Step.mv 31 23, Step.mv 31 24,
     Step.mv 31 25, Step.rw 4 12 1 true, Step.rw 5 11 0 false, Step.mv 7 6, Step.mv 10 9, Step.rw 8 4 1 false,
     Step.mv 6 5, Step.mv 9 8, Step.mv 12 11, Step.mv 13 12, Step.rw 5 10 0 true, Step.mv 17 16, Step.mv 19 17,
     Step.rw 1 16 2 true, Step.mv 17 18, Step.mv 18 17, Step.mv 20 18, Step.mv 21 20, Step.rw 3 17 0 true, Step.mv 18 19,
     Step.rw 1 0 2 true, Step.rw 1 0 1 true, Step.mv 1 2, Step.rw 3 2 1 true, Step.mv 5 4, Step.mv 8 7, Step.mv 12 11,
     Step.mv 15 14, Step.mv 19 18, Step.mv 25 24, Step.mv 27 26, Step.mv 29 28, Step.rw 6 3 0 false])
    (by decide +kernel)

end QCert.SelingerClifford
