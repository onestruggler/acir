/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): generators and relations

M. Amy, N. J. Ross, S. Wesley, *A sound and complete equational theory for
3-qubit Toffoli–Hadamard circuits*, QPL 2024 (arXiv:2407.11152).

The alphabet `Σ₁` of Theorem 5.2 is the set `Σ_D` of Toffoli–K gates of
Section 4.1 (`X_j`, `CX_{j,k}`, `CCX_{j,k}`, `Z_j`, `CZ_{j,k}`, `K_{j,j+1}`,
`σ_{j,k}`) together with the four-level operator `K_[0,1,2,3]` and `CCZ`
(Section 5.6); `Σ₂ = Σ₁ ∪ {H₂}` (Section 6).  Qubits are numbered `0, 1, 2`
as in the paper, qubit `0` being the most significant (the first tensor
factor; in the framework's wire numbering, where wire `0` is the least
significant digit, paper qubit `j` is wire `2 - j`).  States `0, …, 7`
of the multi-level operators are `4 x₀ + 2 x₁ + x₂`, indices from `0` as in
the paper.

The relations, numbered as printed:

* `Fig4`, Figure 4: the relations `R₀` for `W(E₈)`, (1)–(46);
* `Fig7`, Figure 7: the relations `R₈⁴`, (83)–(101), which extend `R₀` to
  `O(8, 𝔻)`; they are written with abbreviations for multi-level operators
  (Sections 5.3 and 5.6), `xab`, `negw`, `kw`, `rho` below;
* `rK`, the relation `(r_K)` of Section 5.5, which is in neither figure:
  `R₁ = R₀ ∪ R₈⁴ ∪ {r_K}` (Theorem 5.2, corrected);
* `Fig8`, Figure 8, (102)–(108): `R₂ = R₁ ∪` Figure 8 (Theorem 6.3).

## Misprints, used corrected (each checked on 8 × 8 matrices)

* (33) is printed `CCX_{0,1} ≈ σ_{1,2} CCX_{0,2} σ_{0,2}`, which is false;
  it is `CCX_{0,1} ≈ σ_{1,2} CCX_{0,2} σ_{1,2}`.
* The alias `(−1)_[0] = X₀ X₁ CCZ X₁ X₀` of Section 5.6 is `(−1)_[1]`; the
  alias is `X₀ X₁ X₂ CCZ X₂ X₁ X₀`.  (With the printed alias (85), (94),
  (97), (98) and (101) are false.)
* (97) is printed `X_[0,1] K_[0,1,2,3] ≈ K_[0,1,2,3] X_[0,1] (−1)_[1] (−1)_[3]`,
  which is false; the relation (4a) of Li–Ross–Selinger it stands for is
  `X_[0,1] K_[0,1,2,3] ≈ K_[0,1,2,3] X_[1,3] (−1)_[1] (−1)_[3]`.
* (100) is printed `K_[0,1,2,3] K_[1,3,4,5] ≈ K_[1,3,4,5] K_[0,1,2,3]`, which
  is false (the two do not commute); the relation (5a) of Li–Ross–Selinger
  it stands for is `K_[0,1,2,3] K_[1,3,4,5] ≈ K_[2,3,4,5] K_[0,1,2,4]`.
  (Both slips come from the transcription of Li–Ross–Selinger's Table 1 in
  Figure 5, relations (63) and (66), and recur in Figures 6 and 10.)
* The abbreviations `X_[1,3]`, `X_[0,4]` of Figure 7 are not spelled out;
  `X_[a,b]` for `b > a + 1` is taken to be `X_[a,a+1] X_[a+1,b] X_[a,a+1]`
  (relation (76) of Figure 6, `X_[a,a+2] = X_[a,a+1] X_[a+1,a+2] X_[a,a+1]`,
  extended to any `b`, read as a definition).
-/
import QCert.Presentation

namespace QCert.ToffoliHadamard

/-- The alphabet `Σ₁`: the Toffoli–K gates `Σ_D` of Section 4.1, and
`K_[0,1,2,3]` and `CCZ` of Section 5.6. -/
inductive Sym1 : Type
  /-- `X_j`: `X` on qubit `j`. -/
  | X0 | X1 | X2
  /-- `CX_{j,k}`: `X` on qubit `k` controlled by qubit `j`. -/
  | CX01 | CX02 | CX10 | CX12 | CX20 | CX21
  /-- `CCX_{j,k}`: `X` on the third qubit controlled by qubits `j`, `k`. -/
  | CCX01 | CCX02 | CCX12
  /-- `Z_j`. -/
  | Z0 | Z1 | Z2
  /-- `CZ_{j,k}`. -/
  | CZ01 | CZ02 | CZ12
  /-- `K_{j,j+1} = H_j H_{j+1}`. -/
  | K01 | K12
  /-- `σ_{j,k}`: the swap of qubits `j` and `k`. -/
  | S01 | S02 | S12
  /-- `K_[0,1,2,3]`, the four-level operator of type `K` (a `K_{1,2}`
  controlled negatively by qubit `0`). -/
  | Kc
  /-- `CCZ = (−1)_[7]`. -/
  | CCZ
  deriving DecidableEq

/-- The alphabet `Σ₂ = Σ₁ ∪ {H₂}` of Section 6. -/
inductive Sym2 : Type
  /-- A letter of `Σ₁`. -/
  | g (x : Sym1)
  /-- `H₂`: the Hadamard gate on qubit `2`. -/
  | H2
  deriving DecidableEq

open Sym1

/-- A word over `Σ₁`, written as a list. -/
abbrev w (l : List Sym1) : Word Sym1 := FreeMonoid.ofList l

/-! ## Abbreviations of Sections 5.3 and 5.6 -/

/-- `X_[a,a+1]` as a circuit over `Σ_D` (Section 5.6). -/
def xAdj : ℕ → List Sym1
  | 0 => [X0, X1, CCX01, X1, X0]
  | 1 => [X0, CCX01, CCX02, CCX01, X0]
  | 2 => [X0, CCX01, X0]
  | 3 => [X0, X2, CCX01, X0, CCX12, CCX02, CCX12, X0, CCX01, X2, X0]
  | 4 => [X1, CCX01, X1]
  | 5 => [CCX01, CCX02, CCX01]
  | _ => [CCX01]

/-- `X_[a,a+g+1]`, by `X_[a,b] = X_[a,a+1] X_[a+1,b] X_[a,a+1]`. -/
def xGap : ℕ → ℕ → List Sym1
  | 0, a => xAdj a
  | g + 1, a => xAdj a ++ xGap g (a + 1) ++ xAdj a

/-- `X_[a,b]`, `a < b`. -/
def xab (a b : ℕ) : List Sym1 := xGap (b - a - 1) a

/-- `(−1)_[0]`, the alias of Section 5.6 (corrected): `X₀ X₁ X₂ CCZ X₂ X₁ X₀`. -/
def neg0 : List Sym1 := [X0, X1, X2, CCZ, X2, X1, X0]

/-- `(−1)_[c] = X_[0,c] (−1)_[0] X_[0,c]` (Section 5.3). -/
def negw (c : ℕ) : List Sym1 := if c = 0 then neg0 else xab 0 c ++ neg0 ++ xab 0 c

/-- Conjugation by `X_[i,j]` (nothing when `i = j`). -/
def conjX (i j : ℕ) (u : List Sym1) : List Sym1 := if i = j then u else xab i j ++ u ++ xab i j

/-- `K_[a,b,c,d] = X_[0,a] X_[1,b] X_[2,c] X_[3,d] K_[0,1,2,3] X_[3,d] X_[2,c] X_[1,b] X_[0,a]`
(Section 5.3). -/
def kw (a b c d : ℕ) : List Sym1 := conjX 0 a (conjX 1 b (conjX 2 c (conjX 3 d [Kc])))

/-- `ρ = K_[4,5,6,7] K_[0,1,2,3] X_[3,4] K_[0,1,2,3] K_[4,5,6,7]` (Figure 6). -/
def rho : List Sym1 := kw 4 5 6 7 ++ [Kc] ++ xab 3 4 ++ [Kc] ++ kw 4 5 6 7

/-! ## The relations -/

/-- Figure 4: the relations `R₀` for `W(E₈)` ((33) corrected). -/
inductive Fig4 : WRel Sym1
  | r1 : Fig4 (w [CZ01]) (w [K12, CX01, K12])
  | r2 : Fig4 (w [X1]) (w [CX01, X0, CX01, X0])
  | r3 : Fig4 (w [Z0]) (w [CZ01, CX01, CZ01, CX01])
  | r4 : Fig4 (w [Z1]) (w [K12, X1, K12])
  | r5 : Fig4 (w [CX20]) (w [X1, CCX12, X1, CCX12])
  | r6 : Fig4 (w [CX21]) (w [CX20, CX01, CX20, CX01])
  | r7 : Fig4 (w [CX12]) (w [K12, CX21, K12])
  | r8 : Fig4 (w [S12]) (w [CX12, CX21, CX12])
  | r9 : Fig4 (w [CX02]) (w [S12, CX01, S12])
  | r10 : Fig4 (w [S02]) (w [CX02, CX20, CX02])
  | r11 : Fig4 (w [K01]) (w [S02, K12, S02])
  | r12 : Fig4 (w [CX10]) (w [K01, CX01, K01])
  | r13 : Fig4 (w [S01]) (w [CX01, CX10, CX01])
  | r14 : Fig4 (w [CCX02]) (w [S01, CCX12, S01])
  | r15 : Fig4 (w [X2]) (w [S02, X0, S02])
  | r16 : Fig4 (w [Z2]) (w [S02, Z0, S02])
  | r17 : Fig4 (w [CCX01]) (w [K12, CCX02, K12])
  | r18 : Fig4 (w [CZ02]) (w [S12, CZ01, S12])
  | r19 : Fig4 (w [CZ12]) (w [S01, CZ02, S01])
  | r20 : Fig4 (w [S12]) (w [CZ12, K12, CZ12, K12, CZ12, K12])
  | r21 : Fig4 (w [X0, X0]) (w [])
  | r22 : Fig4 (w [CX01, CX01]) (w [])
  | r23 : Fig4 (w [K12, K12]) (w [])
  | r24 : Fig4 (w [CCX12, CCX12]) (w [])
  | r25 : Fig4 (w [K01, K01]) (w [])
  | r26 : Fig4 (w [CX12, X0]) (w [X0, CX12])
  | r27 : Fig4 (w [X0, K12]) (w [K12, X0])
  | r28 : Fig4 (w [X1]) (w [S01, X0, S01])
  | r29 : Fig4 (w [CX20]) (w [S02, CX02, S02])
  | r30 : Fig4 (w [CX12]) (w [S01, CX02, S01])
  | r31 : Fig4 (w [CX21]) (w [S01, CX20, S01])
  | r32 : Fig4 (w [CCX01]) (w [S02, CCX12, S02])
  /-- (33), corrected: printed `σ_{1,2} CCX_{0,2} σ_{0,2}`. -/
  | r33 : Fig4 (w [CCX01]) (w [S12, CCX02, S12])
  | r34 : Fig4 (w [Z1]) (w [S01, Z0, S01])
  | r35 : Fig4 (w [K01]) (w [S01, K01, S01])
  | r36 : Fig4 (w [CCX12, CX10]) (w [CX10, CCX12])
  | r37 : Fig4 (w [X0, CCX12]) (w [CCX12, X0])
  | r38 : Fig4 (w [X0, CX10]) (w [CX10, X0])
  | r39 : Fig4 (w [K01, K12]) (w [K12, K01])
  | r40 : Fig4 (w [CZ01, CZ12]) (w [CZ12, CZ01])
  | r41 : Fig4 (w [K01, Z0]) (w [X0, K01])
  | r42 : Fig4 (w [X0, CCX01]) (w [CCX01, CX12, X0])
  | r43 : Fig4 (w [CX01, CZ12]) (w [CZ12, CZ02, CX01])
  | r44 : Fig4 (w [CX12, CCX12]) (w [CCX12, CX10, CX12])
  | r45 : Fig4 (w [CCX12, CX01]) (w [CX01, CCX02, CCX12, CCX02])
  | r46 : Fig4 (w [CCX01, CCX02]) (w [CCX02, CCX01, CCX02, CCX01])

/-- Figure 7: the relations `R₈⁴` (the alias of `(−1)_[0]`, (97) and (100)
corrected; see the module docstring). -/
inductive Fig7 : WRel Sym1
  | r83 : Fig7 (w (negw 0 ++ negw 0)) (w [])
  | r84 : Fig7 (w [Kc, Kc]) (w [])
  | r85 : Fig7 (w (xab 1 2 ++ negw 0)) (w (negw 0 ++ xab 1 2))
  | r86 : Fig7 (w (xab 2 3 ++ negw 0)) (w (negw 0 ++ xab 2 3))
  | r87 : Fig7 (w (xab 3 4 ++ negw 0)) (w (negw 0 ++ xab 3 4))
  | r88 : Fig7 (w (xab 4 5 ++ negw 0)) (w (negw 0 ++ xab 4 5))
  | r89 : Fig7 (w (xab 5 6 ++ negw 0)) (w (negw 0 ++ xab 5 6))
  | r90 : Fig7 (w (xab 6 7 ++ negw 0)) (w (negw 0 ++ xab 6 7))
  | r91 : Fig7 (w (xab 4 5 ++ [Kc])) (w ([Kc] ++ xab 4 5))
  | r92 : Fig7 (w (xab 5 6 ++ [Kc])) (w ([Kc] ++ xab 5 6))
  | r93 : Fig7 (w (xab 6 7 ++ [Kc])) (w ([Kc] ++ xab 6 7))
  | r94 : Fig7 (w (negw 4 ++ [Kc])) (w ([Kc] ++ negw 4))
  | r95 : Fig7 (w (negw 0 ++ negw 4)) (w (negw 4 ++ negw 0))
  | r96 : Fig7 (w ([Kc] ++ kw 4 5 6 7)) (w (kw 4 5 6 7 ++ [Kc]))
  /-- (97), corrected: printed `K_[0,1,2,3] X_[0,1] (−1)_[1] (−1)_[3]`. -/
  | r97 : Fig7 (w (xab 0 1 ++ [Kc])) (w ([Kc] ++ xab 1 3 ++ negw 1 ++ negw 3))
  | r98 : Fig7 (w (xab 1 2 ++ [Kc])) (w (negw 0 ++ [Kc] ++ negw 0 ++ [Kc] ++ negw 0))
  | r99 : Fig7 (w (xab 2 3 ++ [Kc])) (w ([Kc] ++ xab 1 3))
  /-- (100), corrected: printed `K_[1,3,4,5] K_[0,1,2,3]` on the right. -/
  | r100 : Fig7 (w ([Kc] ++ kw 1 3 4 5)) (w (kw 2 3 4 5 ++ kw 0 1 2 4))
  | r101 : Fig7 (w (negw 0 ++ negw 4 ++ xab 0 4 ++ rho)) (w (rho ++ xab 0 4 ++ negw 4 ++ negw 0))

/-- The right-hand side of `(r_K)`: `K_[4,5,6,7] X₀ K_[4,5,6,7] X₀`. -/
def rKrhs : List Sym1 := kw 4 5 6 7 ++ [X0] ++ kw 4 5 6 7 ++ [X0]

/-- The relations `R₀ ∪ R₈⁴` of Figures 4 and 7, as Theorem 5.2 states
them (without `(r_K)`). -/
inductive Fig47 : WRel Sym1
  | fig4 {u v : Word Sym1} (h : Fig4 u v) : Fig47 u v
  | fig7 {u v : Word Sym1} (h : Fig7 u v) : Fig47 u v

/-- `R₁`: Figures 4 and 7 and `(r_K) K_{1,2} ≈ K_[4,5,6,7] X₀ K_[4,5,6,7] X₀`
(Section 5.5), the presentation of `O(8, 𝔻)` of Theorem 5.2 corrected. -/
inductive R1 : WRel Sym1
  | fig4 {u v : Word Sym1} (h : Fig4 u v) : R1 u v
  | fig7 {u v : Word Sym1} (h : Fig7 u v) : R1 u v
  /-- `(r_K)` of Section 5.5. -/
  | rK : R1 (w [K12]) (w rKrhs)

/-- A word over `Σ₁` as a word over `Σ₂`. -/
abbrev up : Word Sym1 →* Word Sym2 := FreeMonoid.map Sym2.g

/-- A word over `Σ₂`, written as a list of letters of `Σ₁` and `H₂`. -/
abbrev w2 (l : List Sym2) : Word Sym2 := FreeMonoid.ofList l

/-- Figure 8: the relations added for `TofH(3)`, (102)–(108). -/
inductive Fig8 : WRel Sym2
  | r102 : Fig8 (w2 [.H2, .g X0]) (w2 [.g X0, .H2])
  | r103 : Fig8 (w2 [.H2, .g CX01]) (w2 [.g CX01, .H2])
  | r104 : Fig8 (w2 [.H2, .g CCX12]) (w2 [.g K01, .g K12, .g CCZ, .g K12, .g K01, .H2])
  | r105 : Fig8 (w2 [.H2, .g CCZ]) (w2 [.g CCX01, .H2])
  | r106 : Fig8 (w2 [.H2, .g K12]) (w2 [.g K12, .H2])
  | r107 : Fig8 (w2 [.H2, .g Kc]) (w2 [.g Kc, .H2])
  | r108 : Fig8 (w2 [.H2, .H2]) (w2 [])

/-- `R₂ = R₁ ∪` Figure 8 (Section 6). -/
inductive R2 : WRel Sym2
  | r1 {u v : Word Sym1} (h : R1 u v) : R2 (up u) (up v)
  | fig8 {u v : Word Sym2} (h : Fig8 u v) : R2 u v

end QCert.ToffoliHadamard
