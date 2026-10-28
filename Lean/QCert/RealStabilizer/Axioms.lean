/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: the relations as equations of letters

The reduced relations R1-R16 of Figure 1 as equations between words of
letters (time order, our wire numbering), each holding on every number of
wires at least its own (`Holds.of_rel`).
-/
import QCert.RealStabilizer.Relator

namespace QCert.RealStabilizer

set_option maxRecDepth 8000

/-- R1 of Figure 1: `(-1)(-1) = 1`. -/
def eR1 : Eqn :=
  ⟨0, [.neg, .neg],
    []⟩

theorem hR1 : Holds eR1.k eR1.l eR1.r :=
  Holds.of_rel Rel.R1 _ _ rfl rfl (by decide) (by decide)

/-- R2 of Figure 1. -/
def eR2 : Eqn :=
  ⟨1, [.Z 0, .Z 0],
    []⟩

theorem hR2 : Holds eR2.k eR2.l eR2.r :=
  Holds.of_rel Rel.R2 _ _ rfl rfl (by decide) (by decide)

/-- R3 of Figure 1. -/
def eR3 : Eqn :=
  ⟨1, [.H 0, .H 0],
    []⟩

theorem hR3 : Holds eR3.k eR3.l eR3.r :=
  Holds.of_rel Rel.R3 _ _ rfl rfl (by decide) (by decide)

/-- R4 of Figure 1. -/
def eR4 : Eqn :=
  ⟨1, [.Z 0, .H 0, .Z 0, .H 0, .Z 0, .H 0, .Z 0, .H 0],
    [.neg]⟩

theorem hR4 : Holds eR4.k eR4.l eR4.r :=
  Holds.of_rel Rel.R4 _ _ rfl rfl (by decide) (by decide)

/-- R5 of Figure 1. -/
def eR5 : Eqn :=
  ⟨2, [.CZ 0, .CZ 0],
    []⟩

theorem hR5 : Holds eR5.k eR5.l eR5.r :=
  Holds.of_rel Rel.R5 _ _ rfl rfl (by decide) (by decide)

/-- R6 of Figure 1. -/
def eR6 : Eqn :=
  ⟨2, [.Z 1, .CZ 0],
    [.CZ 0, .Z 1]⟩

theorem hR6 : Holds eR6.k eR6.l eR6.r :=
  Holds.of_rel Rel.R6 _ _ rfl rfl (by decide) (by decide)

/-- R7 of Figure 1. -/
def eR7 : Eqn :=
  ⟨2, [.Z 0, .CZ 0],
    [.CZ 0, .Z 0]⟩

theorem hR7 : Holds eR7.k eR7.l eR7.r :=
  Holds.of_rel Rel.R7 _ _ rfl rfl (by decide) (by decide)

/-- R8 of Figure 1.  As `Syntax` states it. -/
def eR8_rel : Eqn :=
  ⟨2, [.H 1, .Z 1, .H 1, .CZ 0],
    [.CZ 0, .H 1, .Z 0, .Z 1, .H 1]⟩

theorem hR8_rel : Holds eR8_rel.k eR8_rel.l eR8_rel.r :=
  Holds.of_rel Rel.R8 _ _ rfl rfl (by decide) (by decide)

/-- The same, as the derivations use it. -/
def eR8 : Eqn :=
  ⟨2, [.H 1, .Z 1, .H 1, .CZ 0],
    [.CZ 0, .H 1, .Z 1, .Z 0, .H 1]⟩

theorem hR8 : Holds eR8.k eR8.l eR8.r :=
  Holds.of_derives (db_ok_cons hR8_rel db_ok_nil)
    (steps := [.rw 0 0 0 false, .mv 3 2])
    (by decide +kernel)
/-- R9 of Figure 1. -/
def eR9 : Eqn :=
  ⟨2, [.H 0, .Z 0, .H 0, .CZ 0],
    [.CZ 0, .H 0, .Z 0, .Z 1, .H 0]⟩

theorem hR9 : Holds eR9.k eR9.l eR9.r :=
  Holds.of_rel Rel.R9 _ _ rfl rfl (by decide) (by decide)

/-- R10 of Figure 1.  As `Syntax` states it. -/
def eR10_rel : Eqn :=
  ⟨2, [.H 1, .CZ 0, .H 1, .CZ 0],
    [.CZ 0, .H 1, .CZ 0, .Z 0, .H 1]⟩

theorem hR10_rel : Holds eR10_rel.k eR10_rel.l eR10_rel.r :=
  Holds.of_rel Rel.R10 _ _ rfl rfl (by decide) (by decide)

/-- The same, as the derivations use it. -/
def eR10 : Eqn :=
  ⟨2, [.H 1, .CZ 0, .H 1, .CZ 0],
    [.CZ 0, .H 1, .CZ 0, .H 1, .Z 0]⟩

theorem hR10 : Holds eR10.k eR10.l eR10.r :=
  Holds.of_derives (db_ok_cons hR10_rel db_ok_nil)
    (steps := [.rw 0 0 0 false, .mv 4 3])
    (by decide +kernel)
/-- R11 of Figure 1. -/
def eR11 : Eqn :=
  ⟨2, [.H 0, .CZ 0, .H 0, .CZ 0],
    [.CZ 0, .H 0, .CZ 0, .H 0, .Z 1]⟩

theorem hR11 : Holds eR11.k eR11.l eR11.r :=
  Holds.of_rel Rel.R11 _ _ rfl rfl (by decide) (by decide)

/-- R12 of Figure 1. -/
def eR12 : Eqn :=
  ⟨2, [.H 0, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0],
    [.CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 1]⟩

theorem hR12 : Holds eR12.k eR12.l eR12.r :=
  Holds.of_rel Rel.R12 _ _ rfl rfl (by decide) (by decide)

/-- R13 of Figure 1. -/
def eR13 : Eqn :=
  ⟨3, [.CZ 1, .CZ 0],
    [.CZ 0, .CZ 1]⟩

theorem hR13 : Holds eR13.k eR13.l eR13.r :=
  Holds.of_rel Rel.R13 _ _ rfl rfl (by decide) (by decide)

/-- R14 of Figure 1.  As `Syntax` states it. -/
def eR14_rel : Eqn :=
  ⟨3, [.H 0, .CZ 0, .H 0, .H 1, .CZ 0, .H 1, .CZ 1, .H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0],
    [.H 2, .CZ 1, .H 1, .H 2, .CZ 1, .H 1, .CZ 0, .H 1, .CZ 1, .H 1, .H 2, .CZ 1, .H 2]⟩

theorem hR14_rel : Holds eR14_rel.k eR14_rel.l eR14_rel.r :=
  Holds.of_rel Rel.R14 _ _ rfl rfl (by decide) (by decide)

/-- The same, as the derivations use it. -/
def eR14 : Eqn :=
  ⟨3, [.H 0, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .CZ 1, .H 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0],
    [.H 2, .CZ 1, .H 2, .H 1, .CZ 1, .H 1, .CZ 0, .H 1, .CZ 1, .H 2, .H 1, .CZ 1, .H 2]⟩

theorem hR14 : Holds eR14.k eR14.l eR14.r :=
  Holds.of_derives (db_ok_cons hR14_rel db_ok_nil)
    (steps := [.mv 3 2, .rw 0 0 0 false, .mv 3 2, .mv 10 9])
    (by decide +kernel)
/-- R15 of Figure 1.  As `Syntax` states it. -/
def eR15_rel : Eqn :=
  ⟨3, [.CZ 1, .H 1, .H 2, .CZ 1, .H 1, .H 2, .CZ 0, .CZ 1, .H 1, .H 2, .CZ 1, .H 1, .H 2,
       .CZ 0],
    [.CZ 0, .H 1, .H 2, .CZ 1, .H 1, .H 2, .CZ 1]⟩

theorem hR15_rel : Holds eR15_rel.k eR15_rel.l eR15_rel.r :=
  Holds.of_rel Rel.R15 _ _ rfl rfl (by decide) (by decide)

/-- The same, as the derivations use it. -/
def eR15 : Eqn :=
  ⟨3, [.CZ 1, .H 2, .H 1, .CZ 1, .H 2, .H 1, .CZ 0, .CZ 1, .H 2, .H 1, .CZ 1, .H 2, .H 1,
       .CZ 0],
    [.CZ 0, .H 2, .H 1, .CZ 1, .H 2, .H 1, .CZ 1]⟩

theorem hR15 : Holds eR15.k eR15.l eR15.r :=
  Holds.of_derives (db_ok_cons hR15_rel db_ok_nil)
    (steps := [.mv 2 1, .mv 5 4, .mv 9 8, .mv 12 11, .rw 0 0 0 false, .mv 2 1, .mv 5 4])
    (by decide +kernel)
/-- R16 of Figure 1.  As `Syntax` states it. -/
def eR16_rel : Eqn :=
  ⟨3, [.CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1,
       .CZ 1],
    [.CZ 1, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 0]⟩

theorem hR16_rel : Holds eR16_rel.k eR16_rel.l eR16_rel.r :=
  Holds.of_rel Rel.R16 _ _ rfl rfl (by decide) (by decide)

/-- The same, as the derivations use it. -/
def eR16 : Eqn :=
  ⟨3, [.CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 1, .CZ 0, .H 1, .H 0, .CZ 0, .H 1, .H 0,
       .CZ 1],
    [.CZ 1, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 0]⟩

theorem hR16 : Holds eR16.k eR16.l eR16.r :=
  Holds.of_derives (db_ok_cons hR16_rel db_ok_nil)
    (steps := [.mv 2 1, .mv 5 4, .mv 9 8, .mv 12 11, .rw 0 0 0 false, .mv 2 1, .mv 5 4])
    (by decide +kernel)
end QCert.RealStabilizer
