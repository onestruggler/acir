/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): the relations as equations of letters

The relations C1–C15 of Figure 8 as equations between words of letters
(time order, our wire numbering), each holding on every number of wires at
least its own (`Holds.of_rel`).
-/
import QCert.SelingerClifford.Rewrite

namespace QCert.SelingerClifford

set_option maxRecDepth 8000

/-- C1 of Figure 8. -/
def eC1 : Eqn :=
  ⟨0, [.om, .om, .om, .om, .om, .om, .om, .om],
    []⟩

theorem hC1 : Holds eC1.k eC1.l eC1.r :=
  Holds.of_rel Rel.C1 _ _ rfl rfl (by decide) (by decide)

/-- C2 of Figure 8. -/
def eC2 : Eqn :=
  ⟨1, [.H 0, .H 0],
    []⟩

theorem hC2 : Holds eC2.k eC2.l eC2.r :=
  Holds.of_rel Rel.C2 _ _ rfl rfl (by decide) (by decide)

/-- C3 of Figure 8. -/
def eC3 : Eqn :=
  ⟨1, [.S 0, .S 0, .S 0, .S 0],
    []⟩

theorem hC3 : Holds eC3.k eC3.l eC3.r :=
  Holds.of_rel Rel.C3 _ _ rfl rfl (by decide) (by decide)

/-- C4 of Figure 8. -/
def eC4 : Eqn :=
  ⟨1, [.H 0, .S 0, .H 0, .S 0, .H 0, .S 0],
    [.om]⟩

theorem hC4 : Holds eC4.k eC4.l eC4.r :=
  Holds.of_rel Rel.C4 _ _ rfl rfl (by decide) (by decide)

/-- C5 of Figure 8. -/
def eC5 : Eqn :=
  ⟨2, [.CZ 0, .CZ 0],
    []⟩

theorem hC5 : Holds eC5.k eC5.l eC5.r :=
  Holds.of_rel Rel.C5 _ _ rfl rfl (by decide) (by decide)

/-- C6 of Figure 8. -/
def eC6 : Eqn :=
  ⟨2, [.S 1, .CZ 0],
    [.CZ 0, .S 1]⟩

theorem hC6 : Holds eC6.k eC6.l eC6.r :=
  Holds.of_rel Rel.C6 _ _ rfl rfl (by decide) (by decide)

/-- C7 of Figure 8. -/
def eC7 : Eqn :=
  ⟨2, [.S 0, .CZ 0],
    [.CZ 0, .S 0]⟩

theorem hC7 : Holds eC7.k eC7.l eC7.r :=
  Holds.of_rel Rel.C7 _ _ rfl rfl (by decide) (by decide)

/-- C8 of Figure 8. -/
def eC8 : Eqn :=
  ⟨2, [.H 1, .S 1, .S 1, .H 1, .CZ 0],
    [.CZ 0, .S 0, .S 0, .H 1, .S 1, .S 1, .H 1]⟩

theorem hC8 : Holds eC8.k eC8.l eC8.r :=
  Holds.of_rel Rel.C8 _ _ rfl rfl (by decide) (by decide)

/-- C9 of Figure 8. -/
def eC9 : Eqn :=
  ⟨2, [.H 0, .S 0, .S 0, .H 0, .CZ 0],
    [.CZ 0, .S 1, .S 1, .H 0, .S 0, .S 0, .H 0]⟩

theorem hC9 : Holds eC9.k eC9.l eC9.r :=
  Holds.of_rel Rel.C9 _ _ rfl rfl (by decide) (by decide)

/-- C10 of Figure 8. -/
def eC10 : Eqn :=
  ⟨2, [.CZ 0, .H 1, .CZ 0],
    [.S 1, .H 1, .CZ 0, .S 0, .S 1, .H 1, .S 1, .om, .om, .om, .om, .om, .om, .om]⟩

theorem hC10 : Holds eC10.k eC10.l eC10.r :=
  Holds.of_rel Rel.C10 _ _ rfl rfl (by decide) (by decide)

/-- C11 of Figure 8. -/
def eC11 : Eqn :=
  ⟨2, [.CZ 0, .H 0, .CZ 0],
    [.S 0, .H 0, .CZ 0, .S 1, .S 0, .H 0, .S 0, .om, .om, .om, .om, .om, .om, .om]⟩

theorem hC11 : Holds eC11.k eC11.l eC11.r :=
  Holds.of_rel Rel.C11 _ _ rfl rfl (by decide) (by decide)

/-- C12 of Figure 8. -/
def eC12 : Eqn :=
  ⟨3, [.CZ 0, .CZ 1],
    [.CZ 1, .CZ 0]⟩

theorem hC12 : Holds eC12.k eC12.l eC12.r :=
  Holds.of_rel Rel.C12 _ _ rfl rfl (by decide) (by decide)

/-- C13 of Figure 8. -/
def eC13 : Eqn :=
  ⟨3, [.CZ 1, .H 2, .H 1, .CZ 1, .H 1, .H 0, .CZ 0, .H 1, .H 0, .CZ 1, .H 2, .H 1, .CZ 1],
    [.CZ 0, .H 0, .H 1, .CZ 0, .H 1, .H 2, .CZ 1, .H 1, .H 2, .CZ 0, .H 0, .H 1, .CZ 0]⟩

theorem hC13 : Holds eC13.k eC13.l eC13.r :=
  Holds.of_rel Rel.C13 _ _ rfl rfl (by decide) (by decide)

/-- C14 of Figure 8. -/
def eC14 : Eqn :=
  ⟨3, [.CZ 1, .H 2, .H 1, .CZ 1, .H 2, .H 1, .CZ 0, .CZ 1, .H 2, .H 1, .CZ 1, .H 2, .H 1, .CZ 0,
       .CZ 1, .H 2, .H 1, .CZ 1, .H 1, .H 2, .CZ 0],
    []⟩

theorem hC14 : Holds eC14.k eC14.l eC14.r :=
  Holds.of_rel Rel.C14 _ _ rfl rfl (by decide) (by decide)

/-- C15 of Figure 8. -/
def eC15 : Eqn :=
  ⟨3, [.CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 1, .CZ 0, .H 0, .H 1, .CZ 0, .H 0, .H 1, .CZ 1,
       .CZ 0, .H 0, .H 1, .CZ 0, .H 1, .H 0, .CZ 1],
    []⟩

theorem hC15 : Holds eC15.k eC15.l eC15.r :=
  Holds.of_rel Rel.C15 _ _ rfl rfl (by decide) (by decide)

end QCert.SelingerClifford
