/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The equations of the Reidemeister–Schreier hypotheses

The 46 equations of the authors' code (`Equation1.agda` …
`Equation46.agda`), which are the hypotheses of the Reidemeister–Schreier
theorem for the coset data of `Cosets.lean`: Equations 1–8 are
hypothesis (a), one per generator `ω, H₀, H₁, S₀, S₁, T₀, T₁, CZ`, and
Equations 9–46 hypothesis (b), Equation `9 + 2 (k - 1)` for the coset `I`
and relation (Sk) and Equation `10 + 2 (k - 1)` for the coset `Ω`.
-/
import QCert.CliffordT2.Cosets

namespace QCert.CliffordT2

open W Simplified SW

/-- Equation 1: hypothesis (a) for `ω`. -/
theorem eqn1 : Derivable Rel (wordA .ω) (FreeMonoid.of .ω) := by
  sorry

/-- Equation 2: hypothesis (a) for `H₀`. -/
theorem eqn2 : Derivable Rel (wordA .H₀) (FreeMonoid.of .H₀) := by
  sorry

/-- Equation 3: hypothesis (a) for `H₁`. -/
theorem eqn3 : Derivable Rel (wordA .H₁) (FreeMonoid.of .H₁) := by
  sorry

/-- Equation 4: hypothesis (a) for `S₀`. -/
theorem eqn4 : Derivable Rel (wordA .S₀) (FreeMonoid.of .S₀) := by
  sorry

/-- Equation 5: hypothesis (a) for `S₁`. -/
theorem eqn5 : Derivable Rel (wordA .S₁) (FreeMonoid.of .S₁) := by
  sorry

/-- Equation 6: hypothesis (a) for `T₀`. -/
theorem eqn6 : Derivable Rel (wordA .T₀) (FreeMonoid.of .T₀) := by
  sorry

/-- Equation 7: hypothesis (a) for `T₁`. -/
theorem eqn7 : Derivable Rel (wordA .T₁) (FreeMonoid.of .T₁) := by
  sorry

/-- Equation 8: hypothesis (a) for `CZ`. -/
theorem eqn8 : Derivable Rel (wordA .CZ) (FreeMonoid.of .CZ) := by
  sorry

/-- Equation 9: hypothesis (b) for the coset `I` and (S1). -/
theorem eqn9 : Derivable Rel (wordB .I (ω₀ ^ 8)) (wordB .I (1)) := by
  sorry

/-- Equation 10: hypothesis (b) for the coset `Ω` and (S1). -/
theorem eqn10 : Derivable Rel (wordB .Ω (ω₀ ^ 8)) (wordB .Ω (1)) := by
  sorry

/-- Equation 11: hypothesis (b) for the coset `I` and (S2). -/
theorem eqn11 : Derivable Rel (wordB .I (H₀₁ ^ 2)) (wordB .I (1)) := by
  sorry

/-- Equation 12: hypothesis (b) for the coset `Ω` and (S2). -/
theorem eqn12 : Derivable Rel (wordB .Ω (H₀₁ ^ 2)) (wordB .Ω (1)) := by
  sorry

/-- Equation 13: hypothesis (b) for the coset `I` and (S3). -/
theorem eqn13 : Derivable Rel (wordB .I (X₀₁ ^ 2)) (wordB .I (1)) := by
  sorry

/-- Equation 14: hypothesis (b) for the coset `Ω` and (S3). -/
theorem eqn14 : Derivable Rel (wordB .Ω (X₀₁ ^ 2)) (wordB .Ω (1)) := by
  sorry

/-- Equation 15: hypothesis (b) for the coset `I` and (S4). -/
theorem eqn15 : Derivable Rel (wordB .I (X₁₂ ^ 2)) (wordB .I (1)) := by
  sorry

/-- Equation 16: hypothesis (b) for the coset `Ω` and (S4). -/
theorem eqn16 : Derivable Rel (wordB .Ω (X₁₂ ^ 2)) (wordB .Ω (1)) := by
  sorry

/-- Equation 17: hypothesis (b) for the coset `I` and (S5). -/
theorem eqn17 : Derivable Rel (wordB .I (X₂₃ ^ 2)) (wordB .I (1)) := by
  sorry

/-- Equation 18: hypothesis (b) for the coset `Ω` and (S5). -/
theorem eqn18 : Derivable Rel (wordB .Ω (X₂₃ ^ 2)) (wordB .Ω (1)) := by
  sorry

/-- Equation 19: hypothesis (b) for the coset `I` and (S6). -/
theorem eqn19 : Derivable Rel (wordB .I (ω₀ * ω₁)) (wordB .I (ω₁ * ω₀)) := by
  sorry

/-- Equation 20: hypothesis (b) for the coset `Ω` and (S6). -/
theorem eqn20 : Derivable Rel (wordB .Ω (ω₀ * ω₁)) (wordB .Ω (ω₁ * ω₀)) := by
  sorry

/-- Equation 21: hypothesis (b) for the coset `I` and (S7). -/
theorem eqn21 : Derivable Rel (wordB .I (ω₂ * H₀₁)) (wordB .I (H₀₁ * ω₂)) := by
  sorry

/-- Equation 22: hypothesis (b) for the coset `Ω` and (S7). -/
theorem eqn22 : Derivable Rel (wordB .Ω (ω₂ * H₀₁)) (wordB .Ω (H₀₁ * ω₂)) := by
  sorry

/-- Equation 23: hypothesis (b) for the coset `I` and (S8). -/
theorem eqn23 : Derivable Rel (wordB .I (ω₀ * X₁₂)) (wordB .I (X₁₂ * ω₀)) := by
  sorry

/-- Equation 24: hypothesis (b) for the coset `Ω` and (S8). -/
theorem eqn24 : Derivable Rel (wordB .Ω (ω₀ * X₁₂)) (wordB .Ω (X₁₂ * ω₀)) := by
  sorry

/-- Equation 25: hypothesis (b) for the coset `I` and (S9). -/
theorem eqn25 : Derivable Rel (wordB .I (ω₀ * X₂₃)) (wordB .I (X₂₃ * ω₀)) := by
  sorry

/-- Equation 26: hypothesis (b) for the coset `Ω` and (S9). -/
theorem eqn26 : Derivable Rel (wordB .Ω (ω₀ * X₂₃)) (wordB .Ω (X₂₃ * ω₀)) := by
  sorry

/-- Equation 27: hypothesis (b) for the coset `I` and (S10). -/
theorem eqn27 : Derivable Rel (wordB .I (H₀₁ * H₂₃)) (wordB .I (H₂₃ * H₀₁)) := by
  sorry

/-- Equation 28: hypothesis (b) for the coset `Ω` and (S10). -/
theorem eqn28 : Derivable Rel (wordB .Ω (H₀₁ * H₂₃)) (wordB .Ω (H₂₃ * H₀₁)) := by
  sorry

/-- Equation 29: hypothesis (b) for the coset `I` and (S11). -/
theorem eqn29 : Derivable Rel (wordB .I (H₀₁ * X₂₃)) (wordB .I (X₂₃ * H₀₁)) := by
  sorry

/-- Equation 30: hypothesis (b) for the coset `Ω` and (S11). -/
theorem eqn30 : Derivable Rel (wordB .Ω (H₀₁ * X₂₃)) (wordB .Ω (X₂₃ * H₀₁)) := by
  sorry

/-- Equation 31: hypothesis (b) for the coset `I` and (S12). -/
theorem eqn31 : Derivable Rel (wordB .I (X₀₁ * X₂₃)) (wordB .I (X₂₃ * X₀₁)) := by
  sorry

/-- Equation 32: hypothesis (b) for the coset `Ω` and (S12). -/
theorem eqn32 : Derivable Rel (wordB .Ω (X₀₁ * X₂₃)) (wordB .Ω (X₂₃ * X₀₁)) := by
  sorry

/-- Equation 33: hypothesis (b) for the coset `I` and (S13). -/
theorem eqn33 : Derivable Rel (wordB .I (X₀₁ * X₁₂ * X₀₁)) (wordB .I (X₁₂ * X₀₁ * X₁₂)) := by
  sorry

/-- Equation 34: hypothesis (b) for the coset `Ω` and (S13). -/
theorem eqn34 : Derivable Rel (wordB .Ω (X₀₁ * X₁₂ * X₀₁)) (wordB .Ω (X₁₂ * X₀₁ * X₁₂)) := by
  sorry

/-- Equation 35: hypothesis (b) for the coset `I` and (S14). -/
theorem eqn35 : Derivable Rel (wordB .I (X₁₂ * X₂₃ * X₁₂)) (wordB .I (X₂₃ * X₁₂ * X₂₃)) := by
  sorry

/-- Equation 36: hypothesis (b) for the coset `Ω` and (S14). -/
theorem eqn36 : Derivable Rel (wordB .Ω (X₁₂ * X₂₃ * X₁₂)) (wordB .Ω (X₂₃ * X₁₂ * X₂₃)) := by
  sorry

/-- Equation 37: hypothesis (b) for the coset `I` and (S15). -/
theorem eqn37 : Derivable Rel (wordB .I (ω₀ * ω₁ * X₀₁)) (wordB .I (X₀₁ * ω₀ * ω₁)) := by
  sorry

/-- Equation 38: hypothesis (b) for the coset `Ω` and (S15). -/
theorem eqn38 : Derivable Rel (wordB .Ω (ω₀ * ω₁ * X₀₁)) (wordB .Ω (X₀₁ * ω₀ * ω₁)) := by
  sorry

/-- Equation 39: hypothesis (b) for the coset `I` and (S16). -/
theorem eqn39 : Derivable Rel (wordB .I (ω₀ * ω₁ * H₀₁)) (wordB .I (H₀₁ * ω₀ * ω₁)) := by
  sorry

/-- Equation 40: hypothesis (b) for the coset `Ω` and (S16). -/
theorem eqn40 : Derivable Rel (wordB .Ω (ω₀ * ω₁ * H₀₁)) (wordB .Ω (H₀₁ * ω₀ * ω₁)) := by
  sorry

/-- Equation 41: hypothesis (b) for the coset `I` and (S17). -/
theorem eqn41 : Derivable Rel (wordB .I (H₀₁ * X₀₁)) (wordB .I (ω₁ ^ 4 * H₀₁)) := by
  sorry

/-- Equation 42: hypothesis (b) for the coset `Ω` and (S17). -/
theorem eqn42 : Derivable Rel (wordB .Ω (H₀₁ * X₀₁)) (wordB .Ω (ω₁ ^ 4 * H₀₁)) := by
  sorry

/-- Equation 43: hypothesis (b) for the coset `I` and (S18). -/
theorem eqn43 :
    Derivable Rel (wordB .I (H₀₁ * ω₀ ^ 2 * H₀₁)) (wordB .I (ω₀ ^ 6 * H₀₁ * ω₀ ^ 3 * ω₁ ^ 5)) := by
  sorry

/-- Equation 44: hypothesis (b) for the coset `Ω` and (S18). -/
theorem eqn44 :
    Derivable Rel (wordB .Ω (H₀₁ * ω₀ ^ 2 * H₀₁)) (wordB .Ω (ω₀ ^ 6 * H₀₁ * ω₀ ^ 3 * ω₁ ^ 5)) := by
  sorry

/-- Equation 45: hypothesis (b) for the coset `I` and (S19). -/
theorem eqn45 :
    Derivable Rel (wordB .I (H₀₁ * H₂₃ * H₀₂ * H₁₃)) (wordB .I (H₀₂ * H₁₃ * H₀₁ * H₂₃)) := by
  sorry

/-- Equation 46: hypothesis (b) for the coset `Ω` and (S19). -/
theorem eqn46 :
    Derivable Rel (wordB .Ω (H₀₁ * H₂₃ * H₀₂ * H₁₃)) (wordB .Ω (H₀₂ * H₁₃ * H₀₁ * H₂₃)) := by
  sorry

/-- Hypothesis (a) of the Reidemeister–Schreier theorem. -/
theorem hypA (x : Gen) :
    (hstar hT .I (f' x)).2 = .I ∧ Derivable Rel (hstar hT .I (f' x)).1 (FreeMonoid.of x) := by
  refine ⟨cosetA x, ?_⟩
  cases x
  · exact eqn1
  · exact eqn2
  · exact eqn3
  · exact eqn4
  · exact eqn5
  · exact eqn6
  · exact eqn7
  · exact eqn8

/-- Hypothesis (b) of the Reidemeister–Schreier theorem. -/
theorem hypB (c : Coset) (w w' : Word SGen) (h : SRel w w') :
    (hstar hT c w).2 = (hstar hT c w').2 ∧ Derivable Rel (hstar hT c w).1 (hstar hT c w').1 := by
  refine ⟨cosetB c w w' h, ?_⟩
  cases h <;> cases c
  · exact eqn9
  · exact eqn10
  · exact eqn11
  · exact eqn12
  · exact eqn13
  · exact eqn14
  · exact eqn15
  · exact eqn16
  · exact eqn17
  · exact eqn18
  · exact eqn19
  · exact eqn20
  · exact eqn21
  · exact eqn22
  · exact eqn23
  · exact eqn24
  · exact eqn25
  · exact eqn26
  · exact eqn27
  · exact eqn28
  · exact eqn29
  · exact eqn30
  · exact eqn31
  · exact eqn32
  · exact eqn33
  · exact eqn34
  · exact eqn35
  · exact eqn36
  · exact eqn37
  · exact eqn38
  · exact eqn39
  · exact eqn40
  · exact eqn41
  · exact eqn42
  · exact eqn43
  · exact eqn44
  · exact eqn45
  · exact eqn46

end QCert.CliffordT2
