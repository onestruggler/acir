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
    (steps := [.rw 1 0 0 true, .rw 0 3 0 true, .rw 2 4 0 false])
    (by decide +kernel)

/-- (5) of Lemma 1.1: `HSHS = SSSH·ω`. -/
def eL5 : Eqn :=
  ⟨1, [.S 0, .H 0, .S 0, .H 0],
    [.H 0, .S 0, .S 0, .S 0, .om]⟩

theorem hL5 : Holds eL5.k eL5.l eL5.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hL4 db_ok_nil))
    (steps := [.rw 0 0 0 true, .rw 0 0 0 true, .rw 1 3 0 false, .mv 7 8, .rw 0 6 0 false, .rw 0 0 0 false])
    (by decide +kernel)

/-- (6) of Lemma 1.1: `HSSSH = SHS·ω⁻¹`. -/
def eL6 : Eqn :=
  ⟨1, [.H 0, .S 0, .S 0, .S 0, .H 0],
    [.S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]⟩

theorem hL6 : Holds eL6.k eL6.l eL6.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hL4 db_ok_nil)))
    (steps := [.rw 0 5 0 true, .mv 12 5, .rw 2 1 0 true, .rw 1 0 0 false])
    (by decide +kernel)

/-- (7) of Lemma 1.1: `SHSSHS = HSSH·ω²`. -/
def eL7 : Eqn :=
  ⟨1, [.S 0, .H 0, .S 0, .S 0, .H 0, .S 0],
    [.H 0, .S 0, .S 0, .H 0, .om, .om]⟩

theorem hL7 : Holds eL7.k eL7.l eL7.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC3 (db_ok_cons hL6 db_ok_nil))))
    (steps := [.rw 0 6 0 true, .mv 13 3, .mv 13 4, .mv 13 5, .mv 13 6, .mv 13 7, .mv 13 8, .mv 13 9,
     .rw 3 0 0 true, .rw 0 9 0 true, .mv 16 8, .mv 16 9, .mv 16 10, .mv 16 11, .mv 16 12,
     .mv 16 13, .mv 16 14, .rw 3 5 0 true, .rw 1 4 0 false, .rw 2 1 0 false])
    (by decide +kernel)

/-- (8) of Lemma 1.1: `HSSHSS = SSHSSH·ω⁴`. -/
def eL8 : Eqn :=
  ⟨1, [.S 0, .S 0, .H 0, .S 0, .S 0, .H 0],
    [.H 0, .S 0, .S 0, .H 0, .S 0, .S 0, .om, .om, .om, .om]⟩

theorem hL8 : Holds eL8.k eL8.l eL8.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hL5 (db_ok_cons hL6 (db_ok_cons hL7 db_ok_nil))))
    (steps := [.rw 0 6 0 true, .mv 13 4, .mv 13 5, .mv 13 6, .mv 13 7, .mv 13 8, .mv 13 9, .mv 13 10,
     .rw 2 1 0 true, .rw 1 4 0 false, .rw 3 0 0 false, .mv 5 7, .mv 4 6])
    (by decide +kernel)

/-- (9) of Lemma 1.1: `SSSHSSH = HSSHS·ω⁻²`. -/
def eL9 : Eqn :=
  ⟨1, [.H 0, .S 0, .S 0, .H 0, .S 0, .S 0, .S 0],
    [.S 0, .H 0, .S 0, .S 0, .H 0, .om, .om, .om, .om, .om, .om]⟩

theorem hL9 : Holds eL9.k eL9.l eL9.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hL5 db_ok_nil)))
    (steps := [.rw 0 7 0 true, .mv 14 7, .rw 2 3 0 true, .mv 13 4, .rw 2 0 0 true, .rw 1 3 0 false])
    (by decide +kernel)

/-- (10) of Lemma 1.1: `SSSHSSS = HSH·ω⁻¹`. -/
def eL10 : Eqn :=
  ⟨1, [.S 0, .S 0, .S 0, .H 0, .S 0, .S 0, .S 0],
    [.H 0, .S 0, .H 0, .om, .om, .om, .om, .om, .om, .om]⟩

theorem hL10 : Holds eL10.k eL10.l eL10.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC3 (db_ok_cons hL4 db_ok_nil)))
    (steps := [.rw 0 7 0 true, .mv 14 4, .rw 2 0 0 true, .rw 1 3 0 false])
    (by decide +kernel)

/-- (14) of Lemma 1.2. -/
def eL14 : Eqn :=
  ⟨2, [.S 1, .S 1, .H 1, .CZ 0],
    [.H 1, .CZ 0, .H 1, .S 0, .S 1, .S 0, .S 1, .H 1]⟩

theorem hL14 : Holds eL14.k eL14.l eL14.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC8 db_ok_nil))
    (steps := [.rw 0 0 1 true, .rw 1 1 0 false, .mv 4 2, .mv 5 4])
    (by decide +kernel)

/-- The upside-down version of (14) of Lemma 1.2. -/
def eM14 : Eqn :=
  ⟨2, [.S 0, .S 0, .H 0, .CZ 0],
    [.H 0, .CZ 0, .H 0, .S 1, .S 0, .S 1, .S 0, .H 0]⟩

theorem hM14 : Holds eM14.k eM14.l eM14.r :=
  Holds.of_derives (db_ok_cons hC2 (db_ok_cons hC9 db_ok_nil))
    (steps := [.rw 0 0 0 true, .rw 1 1 0 false, .mv 4 2, .mv 5 4])
    (by decide +kernel)

/-- (15) of Lemma 1.2. -/
def eL15 : Eqn :=
  ⟨2, [.H 1, .S 1, .H 1, .CZ 0],
    [.S 1, .H 1, .CZ 0, .S 1, .S 0, .H 1, .S 0, .S 1, .S 1, .H 1, .om, .om, .om, .om, .om, .om,
     .om]⟩

theorem hL15 : Holds eL15.k eL15.l eL15.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC6 (db_ok_cons hL5 (db_ok_cons hL10 (db_ok_cons hL14 db_ok_nil))))))
    (steps := [.rw 0 4 0 true, .mv 11 3, .mv 11 4, .mv 11 5, .mv 11 6, .mv 11 7, .mv 11 8, .mv 11 9,
     .rw 4 0 1 true, .rw 2 6 0 false, .rw 2 5 0 false, .rw 2 4 0 false, .rw 5 1 0 false,
     .mv 5 4, .mv 7 5, .mv 8 6, .mv 9 7, .mv 10 8, .mv 11 9, .mv 12 10, .rw 3 6 1 true,
     .mv 10 7, .mv 11 8, .rw 0 12 0 true, .mv 19 7, .rw 3 3 1 true, .mv 7 4, .mv 8 6,
     .rw 1 8 1 false])
    (by decide +kernel)

/-- The upside-down version of (15) of Lemma 1.2. -/
def eM15 : Eqn :=
  ⟨2, [.H 0, .S 0, .H 0, .CZ 0],
    [.S 0, .H 0, .CZ 0, .S 0, .S 1, .H 0, .S 1, .S 0, .S 0, .H 0, .om, .om, .om, .om, .om, .om,
     .om]⟩

theorem hM15 : Holds eM15.k eM15.l eM15.r :=
  Holds.of_derives (db_ok_cons hC1 (db_ok_cons hC2 (db_ok_cons hC7 (db_ok_cons hL5 (db_ok_cons hL10 (db_ok_cons hM14 db_ok_nil))))))
    (steps := [.rw 0 4 0 true, .mv 11 3, .mv 11 4, .mv 11 5, .mv 11 6, .mv 11 7, .mv 11 8, .mv 11 9,
     .rw 4 0 0 true, .rw 2 6 0 false, .rw 2 5 0 false, .rw 2 4 0 false, .rw 5 1 0 false,
     .mv 5 4, .mv 7 5, .mv 8 6, .mv 9 7, .mv 10 8, .mv 11 9, .mv 12 10, .rw 3 6 0 true,
     .mv 10 7, .mv 11 8, .rw 0 12 0 true, .mv 19 7, .rw 3 3 0 true, .mv 7 4, .mv 8 6,
     .rw 1 8 0 false])
    (by decide +kernel)

/-- (16) of Lemma 1.2. -/
def eL16 : Eqn :=
  ⟨2, [.S 1, .H 1, .CZ 0, .H 0, .H 1, .CZ 0],
    [.H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .S 0, .H 0]⟩

theorem hL16 : Holds eL16.k eL16.l eL16.r := by
  sorry

/-- The upside-down version of (16) of Lemma 1.2. -/
def eM16 : Eqn :=
  ⟨2, [.S 0, .H 0, .CZ 0, .H 1, .H 0, .CZ 0],
    [.H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .S 1, .H 1]⟩

theorem hM16 : Holds eM16.k eM16.l eM16.r := by
  sorry

/-- (17) of Lemma 1.2. -/
def eL17 : Eqn :=
  ⟨2, [.H 1, .CZ 0, .H 0, .S 1, .H 1, .CZ 0],
    [.CZ 0, .H 0, .S 1, .H 1, .CZ 0, .S 0, .S 0, .S 0, .H 0, .S 0, .H 1, .S 1, .S 1, .H 1]⟩

theorem hL17 : Holds eL17.k eL17.l eL17.r := by
  sorry

/-- The upside-down version of (17) of Lemma 1.2. -/
def eM17 : Eqn :=
  ⟨2, [.H 0, .CZ 0, .H 1, .S 0, .H 0, .CZ 0],
    [.CZ 0, .H 1, .S 0, .H 0, .CZ 0, .S 1, .S 1, .S 1, .H 1, .S 1, .H 0, .S 0, .S 0, .H 0]⟩

theorem hM17 : Holds eM17.k eM17.l eM17.r := by
  sorry

/-- (18) of Lemma 1.2. -/
def eL18 : Eqn :=
  ⟨2, [.H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0],
    [.CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0]⟩

theorem hL18 : Holds eL18.k eL18.l eL18.r := by
  sorry

/-- The upside-down version of (18) of Lemma 1.2. -/
def eM18 : Eqn :=
  ⟨2, [.H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 0],
    [.CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1]⟩

theorem hM18 : Holds eM18.k eM18.l eM18.r := by
  sorry

/-- (20) of Lemma 1.3. -/
def eL20 : Eqn :=
  ⟨3, [.CZ 0, .H 1, .H 0, .CZ 1, .H 2, .H 1, .CZ 1, .H 2, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .CZ 1],
    [.H 1, .H 0, .CZ 1, .H 2, .H 1, .CZ 1, .H 2, .CZ 0, .H 1, .H 0, .CZ 0, .H 1]⟩

theorem hL20 : Holds eL20.k eL20.l eL20.r := by
  sorry

/-- The upside-down version of (20) of Lemma 1.3. -/
def eM20 : Eqn :=
  ⟨3, [.CZ 1, .H 1, .H 2, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .CZ 1, .H 1, .H 2, .CZ 1, .H 1, .CZ 0],
    [.H 1, .H 2, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .CZ 1, .H 1, .H 2, .CZ 1, .H 1]⟩

theorem hM20 : Holds eM20.k eM20.l eM20.r := by
  sorry

/-- (21) of Lemma 1.3. -/
def eL21 : Eqn :=
  ⟨3, [.CZ 0, .H 1, .H 0, .CZ 1, .H 1, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 1, .S 1, .H 1,
       .CZ 0],
    [.H 1, .H 0, .CZ 0, .CZ 1, .H 0, .S 1, .S 0, .H 1, .S 0, .S 0]⟩

theorem hL21 : Holds eL21.k eL21.l eL21.r := by
  sorry

/-- The upside-down version of (21) of Lemma 1.3. -/
def eM21 : Eqn :=
  ⟨3, [.CZ 1, .H 1, .H 2, .CZ 0, .H 1, .CZ 1, .H 1, .H 2, .CZ 1, .H 1, .H 2, .CZ 0, .S 1, .H 1,
       .CZ 1],
    [.H 1, .H 2, .CZ 1, .CZ 0, .H 2, .S 1, .S 2, .H 1, .S 2, .S 2]⟩

theorem hM21 : Holds eM21.k eM21.l eM21.r := by
  sorry

end QCert.SelingerClifford
