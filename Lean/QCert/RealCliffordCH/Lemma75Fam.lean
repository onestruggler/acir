/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma 7.5, by equation of Figure 6

Generated: each equation (b1)–(d3) of Figure 6 at every admissible choice of
indices in `0, …, 3`, dispatched to the decoded instances of `Lemma75`.
-/
import QCert.RealCliffordCH.Lemma75

namespace QCert.RealCliffordCH.Two


/-- Decoding Equation (b1). -/
theorem fam_b1 (a b : Fin 4) (hab : a ≠ b) :
    EG ([HadamardPi.Gen.Z a, HadamardPi.Gen.Z b] : List G4) ([HadamardPi.Gen.Z b, HadamardPi.Gen.Z a] : List G4) := by
  fin_cases a <;> fin_cases b
  · exfalso; revert hab; decide
  · exact dI_b1_0_1
  · exact dI_b1_0_2
  · exact dI_b1_0_3
  · exact dI_b1_1_0
  · exfalso; revert hab; decide
  · exact dI_b1_1_2
  · exact dI_b1_1_3
  · exact dI_b1_2_0
  · exact dI_b1_2_1
  · exfalso; revert hab; decide
  · exact dI_b1_2_3
  · exact dI_b1_3_0
  · exact dI_b1_3_1
  · exact dI_b1_3_2
  · exfalso; revert hab; decide

/-- Decoding Equation (b2). -/
theorem fam_b2 (a b c : Fin 4) (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
    EG ([HadamardPi.Gen.Z a, HadamardPi.Gen.X b c hbc] : List G4) ([HadamardPi.Gen.X b c hbc, HadamardPi.Gen.Z a] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_0_1_2
  · exact dI_b2_0_1_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_0_2_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_1_0_2
  · exact dI_b2_1_0_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_1_2_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_2_0_1
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_2_0_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_2_1_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_3_0_1
  · exact dI_b2_3_0_2
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b2_3_1_2
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide

/-- Decoding Equation (b3). -/
theorem fam_b3 (a b c d : Fin 4) (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    EG ([HadamardPi.Gen.X a b hab, HadamardPi.Gen.X c d hcd] : List G4) ([HadamardPi.Gen.X c d hcd, HadamardPi.Gen.X a b hab] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b3_0_1_2_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b3_0_2_1_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b3_0_3_1_2
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b3_1_2_0_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b3_1_3_0_2
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b3_2_3_0_1
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide

/-- Decoding Equation (b4). -/
theorem fam_b4 (a b c : Fin 4) (hbc : b < c) (hab : a ≠ b) (hac : a ≠ c) :
    EG ([HadamardPi.Gen.Z a, HadamardPi.Gen.H b c hbc] : List G4) ([HadamardPi.Gen.H b c hbc, HadamardPi.Gen.Z a] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_0_1_2
  · exact dI_b4_0_1_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_0_2_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_1_0_2
  · exact dI_b4_1_0_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_1_2_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_2_0_1
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_2_0_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_2_1_3
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_3_0_1
  · exact dI_b4_3_0_2
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exact dI_b4_3_1_2
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide
  · exfalso; revert hbc hab hac; decide

/-- Decoding Equation (b5). -/
theorem fam_b5 (a b c d : Fin 4) (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    EG ([HadamardPi.Gen.X a b hab, HadamardPi.Gen.H c d hcd] : List G4) ([HadamardPi.Gen.H c d hcd, HadamardPi.Gen.X a b hab] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b5_0_1_2_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b5_0_2_1_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b5_0_3_1_2
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b5_1_2_0_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b5_1_3_0_2
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b5_2_3_0_1
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide

/-- Decoding Equation (b6). -/
theorem fam_b6 (a b c d : Fin 4) (hab : a < b) (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    EG ([HadamardPi.Gen.H a b hab, HadamardPi.Gen.H c d hcd] : List G4) ([HadamardPi.Gen.H c d hcd, HadamardPi.Gen.H a b hab] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b6_0_1_2_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b6_0_2_1_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b6_0_3_1_2
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b6_1_2_0_3
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b6_1_3_0_2
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exact dI_b6_2_3_0_1
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide
  · exfalso; revert hab hcd hac had hbc hbd; decide

/-- Decoding Equation (c1). -/
theorem fam_c1 (a b : Fin 4) (hab : a < b) :
    EG ([HadamardPi.Gen.Z a, HadamardPi.Gen.X a b hab] : List G4) ([HadamardPi.Gen.X a b hab, HadamardPi.Gen.Z b] : List G4) := by
  fin_cases a <;> fin_cases b
  · exfalso; revert hab; decide
  · exact dI_c1_0_1
  · exact dI_c1_0_2
  · exact dI_c1_0_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exact dI_c1_1_2
  · exact dI_c1_1_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exact dI_c1_2_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide

/-- Decoding Equation (c2). -/
theorem fam_c2 (a b c : Fin 4) (hab : a < b) (hbc : b < c) :
    EG ([HadamardPi.Gen.X b c hbc, HadamardPi.Gen.X a b hab] : List G4) ([HadamardPi.Gen.X a b hab, HadamardPi.Gen.X a c (hab.trans hbc)] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c2_0_1_2
  · exact dI_c2_0_1_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c2_0_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c2_1_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide

/-- Decoding Equation (c3). -/
theorem fam_c3 (a b c : Fin 4) (hab : a < b) (hbc : b < c) :
    EG ([HadamardPi.Gen.X a c (hab.trans hbc), HadamardPi.Gen.X b c hbc] : List G4) ([HadamardPi.Gen.X b c hbc, HadamardPi.Gen.X a b hab] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c3_0_1_2
  · exact dI_c3_0_1_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c3_0_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c3_1_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide

/-- Decoding Equation (c4). -/
theorem fam_c4 (a b c : Fin 4) (hab : a < b) (hbc : b < c) :
    EG ([HadamardPi.Gen.H b c hbc, HadamardPi.Gen.X a b hab] : List G4) ([HadamardPi.Gen.X a b hab, HadamardPi.Gen.H a c (hab.trans hbc)] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c4_0_1_2
  · exact dI_c4_0_1_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c4_0_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c4_1_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide

/-- Decoding Equation (c5). -/
theorem fam_c5 (a b c : Fin 4) (hab : a < b) (hbc : b < c) :
    EG ([HadamardPi.Gen.H a c (hab.trans hbc), HadamardPi.Gen.X b c hbc] : List G4) ([HadamardPi.Gen.X b c hbc, HadamardPi.Gen.H a b hab] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c5_0_1_2
  · exact dI_c5_0_1_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c5_0_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exact dI_c5_1_2_3
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide
  · exfalso; revert hab hbc; decide

/-- Decoding Equation (d1). -/
theorem fam_d1 (a b : Fin 4) (hab : a < b) :
    EG ([HadamardPi.Gen.Z a, HadamardPi.Gen.Z b, HadamardPi.Gen.H a b hab] : List G4) ([HadamardPi.Gen.H a b hab, HadamardPi.Gen.Z a, HadamardPi.Gen.Z b] : List G4) := by
  fin_cases a <;> fin_cases b
  · exfalso; revert hab; decide
  · exact dI_d1_0_1
  · exact dI_d1_0_2
  · exact dI_d1_0_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exact dI_d1_1_2
  · exact dI_d1_1_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exact dI_d1_2_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide

/-- Decoding Equation (d2). -/
theorem fam_d2 (a b : Fin 4) (hab : a < b) :
    EG ([HadamardPi.Gen.Z b, HadamardPi.Gen.H a b hab] : List G4) ([HadamardPi.Gen.H a b hab, HadamardPi.Gen.X a b hab] : List G4) := by
  fin_cases a <;> fin_cases b
  · exfalso; revert hab; decide
  · exact dI_d2_0_1
  · exact dI_d2_0_2
  · exact dI_d2_0_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exact dI_d2_1_2
  · exact dI_d2_1_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exact dI_d2_2_3
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide
  · exfalso; revert hab; decide

/-- Decoding Equation (d3). -/
theorem fam_d3 (a b c d : Fin 4) (hab : a < b) (hcd : c < d) (hac : a < c) (hbd : b < d) (hbc : b ≠ c) :
    EG ([HadamardPi.Gen.H c d hcd, HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd, HadamardPi.Gen.H c d hcd, HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd, HadamardPi.Gen.H c d hcd, HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd, HadamardPi.Gen.H c d hcd, HadamardPi.Gen.H a c hac, HadamardPi.Gen.H b d hbd] : List G4) ([HadamardPi.Gen.H a b hab, HadamardPi.Gen.H c d hcd] : List G4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exact dI_d3_0_1_2_3
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exact dI_d3_0_2_1_3
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide
  · exfalso; revert hab hcd hac hbd hbc; decide

end QCert.RealCliffordCH.Two
