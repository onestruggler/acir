# Generators for the completeness proof (Theorem 4.4)

Python 3 with numpy; run from this folder.

| Script | Does |
| --- | --- |
| `qc.py` | qutrit Clifford circuits as letter lists in time order (`('H', j)`, `('S', j)`, `('CZ', j)` on wires `j, j+1`, `('w',)` for `-ω`); the exact action on Pauli data `(c, a, b)` (the Lean `actGen`), numeric matrices with the paper's `H = (ω² - ω)⁻¹ [ω^{jk}]`, inverse words, the derived gates `X`, `Z`, `SWAP`, `XC` of Figure 5 |
| `check_qc.py` | checks on random circuits on 1–3 wires that the exact Pauli action is conjugation by the matrices |
| `gadgets.py` | breadth-first search for the section gadgets of the stabiliser chain (`α`, `P`, `Q`, `Γ₀₁`, `Γ₀₀`; see the route in `../README.md`) |

Wire 0 is the least significant digit of a basis index, as in the Lean
`ofMat`; a Lean word (operator order) is the reverse of a letter list.

Found gadgets (time order):

* `α₀₁ = []`, `α₀₂ = H²`, `α₁₀ = H³`, `α₁₁ = H³S²`, `α₁₂ = H³S`,
  `α₂₀ = H`, `α₂₁ = H³SH²`, `α₂₂ = HSH`;
* `P₁ = H³SHSH`, `P₂ = HSH²S²H`;
* `Q_{0,i} = S^{2i}`, `Q₁₀ = H²S²H²S`, `Q₁₁ = H²S²H²`, `Q₁₂ = H²S²H²S²`,
  `Q₂₀ = H²SH²S²`, `Q₂₁ = H²SH²S`, `Q₂₂ = H²SH²`;
* `Γ₀₁ = H₀³ CZ H₀` (`Z₀ ↦ Z₀Z₁`), `Γ₀₀ = H₀ CZ H₀ H₁ CZ H₁` (`Z₀ ↦ Z₁`).
