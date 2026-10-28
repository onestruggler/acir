# Generators for the completeness proof (Theorem 4.4)

Python 3 with numpy; run from this folder (in WSL: `python3 <script>`).
Circuits are letter lists in time order: `('H', j)`, `('S', j)`, `('CZ', j)`
on wires `j, j+1`, `('w',)` for `-ω`.  Wire 0 is the least significant
digit of a basis index, as in the Lean `ofMat`; a Lean word (operator
order) is the reverse of a letter list.

| Script | Does |
| --- | --- |
| `qc.py` | the exact action on Pauli data `(c, a, b)` (the Lean `actGen`), numeric matrices with the paper's `H = (ω² - ω)⁻¹ [ω^{jk}]`, inverse words, the derived gates `X`, `Z`, `SWAP`, `XC` of Figure 5 |
| `check_qc.py` | checks on random circuits on 1–3 wires that the exact Pauli action is conjugation by the matrices |
| `cliff.py` | projective Clifford elements as the images of the `X_j`, `Z_j` (`key`), their composition, breadth-first search |
| `gadgets.py` | breadth-first search for the section gadgets (`α`, `P`, `Q`, `Γ₀₁`, `Γ₀₀`) |
| `sections.py` | the sections `sigma`, `tau` of the two Schreier stages (checked on 1–3 wires) and K-words by breadth-first search in the stabilisers |
| `engine.py` | the derivation engine of `Engine.lean` in Python (rule steps, free steps, swaps; `chain` finds the steps between consecutive words) |
| `emit.py`, `mk_lib.py` | Lean source for stored libraries (words as base-9 numbers): `<Name>Data.lean`, `<Name>Chk<j>.lean` (lemmas checked by `decide +kernel`, a chunk per module), `<Name>.lean` |
| `cosets.py`, `cert.py` | coset tables with a deduction order for widths 1 and 2 (`Coset.lean`) |
| `lib2.py`, `facts2.py`, `mk_lib2.py` | the two-wire library (free one-wire segments): the swap lemmas, `X` and the generators of `P` passing `CZ`, and the stabiliser facts of the width-2 certificate; writes `Lib2Data.lean`, `Lib2Chk*.lean`, `Lib2.lean` |
| `mk_cert.py` | writes `Cert1Data.lean`, `Cert2Data.lean` (about 2 minutes) |
| `lib3.py`, `facts3.py`, `mk_lib3.py` | the three-wire lemmas and the 311 local facts of the generic step (free two-wire segments; `python3 facts3.py` checks them in about 30 s); `mk_lib3.py [chunk]` writes `Lib3Data.lean`, `Lib3Chk*.lean` (chunks of 12 lemmas by default), `Lib3.lean` and `Facts3Data.lean` |
| `mk_s12.py` | writes `S12Data.lean`, the K-words of the stage-1 condition on two wires |

Found gadgets (time order):

* `α₀₁ = []`, `α₀₂ = H²`, `α₁₀ = H³`, `α₁₁ = H³S²`, `α₁₂ = H³S`,
  `α₂₀ = H`, `α₂₁ = H³SH²`, `α₂₂ = HSH`;
* `P₁ = H³SHSH`, `P₂ = HSH²S²H`;
* `Q_{0,i} = S^{2i}`, `Q₁₀ = H²S²H²S`, `Q₁₁ = H²S²H²`, `Q₁₂ = H²S²H²S²`,
  `Q₂₀ = H²SH²S²`, `Q₂₁ = H²SH²S`, `Q₂₂ = H²SH²`;
* `Γ₀₁ = H₀³ CZ H₀` (`Z₀ ↦ Z₀Z₁`), `Γ₀₀ = H₀ CZ H₀ H₁ CZ H₁` (`Z₀ ↦ Z₁`).

The proof uses `α`, `Q_{0,i}`, `Γ_{ab} = H₀³ CZ H₀ ⨾ α_{ab}` and the swap
for `Γ₀₀` (`Sections.lean`).
