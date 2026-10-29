/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The decided steps of (337) and (338)

Two rotations, one of them between `P ⊗ P`, commute by one semantic step
without wire `4`.  Only the first two rotations of each expansion are
checked (`rots2`, `srots2`); the other two are their inverses (`chkInvR`,
`chkInvS`), and commutation passes to inverses (Lemma B.5, `Comm.inv`).

Memory (2026-10-29): 21 s, peak 4.4 GB resident, about 1.5 GB of it above the
mapped imports; the two-letter windows of `chkInvR`, `chkInvS` are decided
together.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E336x
import QCert.RealCliffordCH.Sec8.D.N13.E322l

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

/-- The rotations of the expansion that are checked; the others are their inverses. -/
def rots2 (b1 b2 b3 : Bool) : List Lt := [P1 b1 b2 b3, P2 b1 b2 b3]

/-- The rotations with the wires `0, 1` exchanged, one by one. -/
def SR1 (b1 b2 b3 : Bool) : Lt := .g .zx [1] [(0, b1), (2, b2), (3, b3)] false
def SR2 (b1 b2 b3 : Bool) : Lt := .g (Kind.sgnZX (!b1)) [0] [(1, true), (2, b2), (3, b3)] false
def SR3 (b1 b2 b3 : Bool) : Lt := .g (Kind.sgnZX b1) [0] [(1, true), (2, b2), (3, b3)] false
def SR4 (b1 b2 b3 : Bool) : Lt := .g .xz [1] [(0, b1), (2, b2), (3, b3)] false

theorem srots_eq (b1 b2 b3 : Bool) :
    srots b1 b2 b3 = [SR1 b1 b2 b3, SR2 b1 b2 b3, SR3 b1 b2 b3, SR4 b1 b2 b3] := rfl

/-- The same for the rotations with the wires `0, 1` exchanged. -/
def srots2 (b1 b2 b3 : Bool) : List Lt := [SR1 b1 b2 b3, SR2 b1 b2 b3]

/-- `P5 = P1⁻¹`, `P4 = P2⁻¹`. -/
theorem chkInvR : ∀ b1 b2 b3 : Bool,
    check 4 [] [P5 b1 b2 b3, P1 b1 b2 b3] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [P1 b1 b2 b3, P5 b1 b2 b3] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [P4 b1 b2 b3, P2 b1 b2 b3] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [P2 b1 b2 b3, P4 b1 b2 b3] [] [.sem 0 2 [] 4] = true := by
  decide +kernel

/-- `SR4 = SR1⁻¹`, `SR3 = SR2⁻¹`. -/
theorem chkInvS : ∀ b1 b2 b3 : Bool,
    check 4 [] [SR4 b1 b2 b3, SR1 b1 b2 b3] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [SR1 b1 b2 b3, SR4 b1 b2 b3] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [SR3 b1 b2 b3, SR2 b1 b2 b3] [] [.sem 0 2 [] 4] = true ∧
    check 4 [] [SR2 b1 b2 b3, SR3 b1 b2 b3] [] [.sem 0 2 [] 4] = true := by
  decide +kernel

end QCert.RealCliffordCH.Sec8.D.N13
