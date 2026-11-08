/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the relations

Translation of `Syntactics.agda`.  The relations of Amy, Ross and Wesley
(arXiv:2407.11152v3):

* `R0` (Figure 4), 46 relations on the Toffoli-K gates `𝒟`;
* `Fig7` (Figure 7, `R₈₄`), 19 relations on `Σ₁ = 𝒟 ∪ {K_[0,1,2,3], CCZ}`;
* `Fig8` (Figure 8), 7 relations for `H₂`;

and the presentations `R1 = R₀ ∪ R₈₄` (Theorem 5.2) and `R2 = R₁ ∪ Figure 8`
(Theorem 6.3).  Each figure is a relation at every level at which its gates
exist, so a derivation from `R₀` is one at every level.

Corrections (each checked on the matrices, `Soundness`):

* (33) printed `CCX₀₁ = σ₁₂ CCX₀₂ σ₀₂`; it is `σ₁₂ CCX₀₂ σ₁₂`.
* (97) printed `X_[0,1]` on the right; it is `X_[1,3]`, as in
  Li–Ross–Selinger's (4a).
* (100) printed as a commutation of `K_[0,1,2,3]` and `K_[1,3,4,5]`; it is
  Li–Ross–Selinger's (5a), `K_[0,1,2,3] K_[1,3,4,5] = K_[2,3,4,5] K_[0,1,2,4]`.
* The alias `(-1)_[0] = X₀ X₁ CCZ X₁ X₀` of Section 5.6 needs `X₂` as well:
  `(-1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀`.

One relation is missing.  Figure 7 relates `K_[0,1,2,3]` and `CCZ` to the
permutations only, and Figure 4 never mentions them, so nothing in `R₁`
relates `K₁₂` to `K_[0,1,2,3]`: the relation `r_K` of Section 5.5,
`K₁₂ = X₀ K_[0,1,2,3] X₀ K_[0,1,2,3]`, is not derivable from `R₁`
(`Independence`), so `R₁` is not complete; `R1plus` and `R2plus` add it.

The aliases of Figure 7 are words over `Σ₁`: `X_[a,a+1]` are the circuits of
Section 5.6 (`T`), `X_[a,b] = X_[a,a+1] X_[a+1,b] X_[a,a+1]` for `b > a + 1`,
`(-1)_[c] = X_[0,c] (-1)_[0] X_[0,c]` and `K_[a,b,c,d] = X_[0,a] X_[1,b]
X_[2,c] X_[3,d] K_[0,1,2,3] X_[3,d] X_[2,c] X_[1,b] X_[0,a]` (Section 5.3),
with `X_[a,a] = ε`.

Words are the framework's `FreeMonoid`; the Agda's right-nested `•` is
written with the left-associative `*`, the same word.
-/
import QCert.ToffoliHadamardRS.Gates

namespace QCert.ToffoliHadamardRS

open Gate

variable {k : ℕ}

/-! ## Figure 4: `R₀` -/

/-- Figure 4, at every level. -/
inductive R0 : WRel (Gate k)
  | r1 : R0 CZ01 (K12 * CX01 * K12)
  | r2 : R0 X1 (CX01 * X0 * CX01 * X0)
  | r3 : R0 Z0 (CZ01 * CX01 * CZ01 * CX01)
  | r4 : R0 Z1 (K12 * X1 * K12)
  | r5 : R0 CX20 (X1 * CCX12 * X1 * CCX12)
  | r6 : R0 CX21 (CX20 * CX01 * CX20 * CX01)
  | r7 : R0 CX12 (K12 * CX21 * K12)
  | r8 : R0 SW12 (CX12 * CX21 * CX12)
  | r9 : R0 CX02 (SW12 * CX01 * SW12)
  | r10 : R0 SW02 (CX02 * CX20 * CX02)
  | r11 : R0 K01 (SW02 * K12 * SW02)
  | r12 : R0 CX10 (K01 * CX01 * K01)
  | r13 : R0 SW01 (CX01 * CX10 * CX01)
  | r14 : R0 CCX02 (SW01 * CCX12 * SW01)
  | r15 : R0 X2 (SW02 * X0 * SW02)
  | r16 : R0 Z2 (SW02 * Z0 * SW02)
  | r17 : R0 CCX01 (K12 * CCX02 * K12)
  | r18 : R0 CZ02 (SW12 * CZ01 * SW12)
  | r19 : R0 CZ12 (SW01 * CZ02 * SW01)
  | r20 : R0 SW12 (CZ12 * K12 * CZ12 * K12 * CZ12 * K12)
  | r21 : R0 (X0 * X0) 1
  | r22 : R0 (CX01 * CX01) 1
  | r23 : R0 (K12 * K12) 1
  | r24 : R0 (CCX12 * CCX12) 1
  | r25 : R0 (K01 * K01) 1
  | r26 : R0 (CX12 * X0) (X0 * CX12)
  | r27 : R0 (X0 * K12) (K12 * X0)
  | r28 : R0 X1 (SW01 * X0 * SW01)
  | r29 : R0 CX20 (SW02 * CX02 * SW02)
  | r30 : R0 CX12 (SW01 * CX02 * SW01)
  | r31 : R0 CX21 (SW01 * CX20 * SW01)
  | r32 : R0 CCX01 (SW02 * CCX12 * SW02)
  | r33 : R0 CCX01 (SW12 * CCX02 * SW12)
  | r34 : R0 Z1 (SW01 * Z0 * SW01)
  | r35 : R0 K01 (SW01 * K01 * SW01)
  | r36 : R0 (CCX12 * CX10) (CX10 * CCX12)
  | r37 : R0 (X0 * CCX12) (CCX12 * X0)
  | r38 : R0 (X0 * CX10) (CX10 * X0)
  | r39 : R0 (K01 * K12) (K12 * K01)
  | r40 : R0 (CZ01 * CZ12) (CZ12 * CZ01)
  | r41 : R0 (K01 * Z0) (X0 * K01)
  | r42 : R0 (X0 * CCX01) (CCX01 * CX12 * X0)
  | r43 : R0 (CX01 * CZ12) (CZ12 * CZ02 * CX01)
  | r44 : R0 (CX12 * CCX12) (CCX12 * CX10 * CX12)
  | r45 : R0 (CCX12 * CX01) (CX01 * CCX02 * CCX12 * CCX02)
  | r46 : R0 (CCX01 * CCX02) (CCX02 * CCX01 * CCX02 * CCX01)

/-! ## The aliases of Figure 7 -/

/-- `X_[a,a+1]`, the circuits of Section 5.6. -/
def T : ℕ → Word (Gate k)
  | 0 => X0 * X1 * CCX01 * X1 * X0
  | 1 => X0 * CCX01 * CCX02 * CCX01 * X0
  | 2 => X0 * CCX01 * X0
  | 3 => X0 * X2 * CCX01 * X0 * CCX12 * CCX02 * CCX12 * X0 * CCX01 * X2 * X0
  | 4 => X1 * CCX01 * X1
  | 5 => CCX01 * CCX02 * CCX01
  | _ + 6 => CCX01

/-- `X_[a, a+1+d]` (the Agda's `Tʳ`). -/
def TR (a : ℕ) : ℕ → Word (Gate k)
  | 0 => T a
  | d + 1 => T a * TR (a + 1) d * T a

/-- `X_[a,b]`, with `X_[a,a] = ε`. -/
def Xab (a b : ℕ) : Word (Gate k) :=
  match b - a with
  | 0 => 1
  | d + 1 => TR a d

/-- `(-1)_[0]`. -/
def m0 : Word (Gate (k + 1)) := X0 * X1 * X2 * CCZw * X2 * X1 * X0

/-- `(-1)_[c]`. -/
def m (c : ℕ) : Word (Gate (k + 1)) := Xab 0 c * m0 * Xab 0 c

/-- `K_[a,b,c,d]`. -/
def Kq (a b c d : ℕ) : Word (Gate (k + 1)) :=
  Xab 0 a * Xab 1 b * Xab 2 c * Xab 3 d * NKw * Xab 3 d * Xab 2 c * Xab 1 b * Xab 0 a

/-- The substring written `Ω` in Figure 7. -/
def Ω : Word (Gate (k + 1)) := Kq 4 5 6 7 * NKw * T 3 * NKw * Kq 4 5 6 7

/-! ## Figure 7: `R₈₄` -/

/-- Figure 7, at every level from `1`. -/
inductive Fig7 : WRel (Gate (k + 1))
  | r83 : Fig7 (m0 * m0) 1
  | r84 : Fig7 (NKw * NKw) 1
  | r85 : Fig7 (T 1 * m0) (m0 * T 1)
  | r86 : Fig7 (T 2 * m0) (m0 * T 2)
  | r87 : Fig7 (T 3 * m0) (m0 * T 3)
  | r88 : Fig7 (T 4 * m0) (m0 * T 4)
  | r89 : Fig7 (T 5 * m0) (m0 * T 5)
  | r90 : Fig7 (T 6 * m0) (m0 * T 6)
  | r91 : Fig7 (T 4 * NKw) (NKw * T 4)
  | r92 : Fig7 (T 5 * NKw) (NKw * T 5)
  | r93 : Fig7 (T 6 * NKw) (NKw * T 6)
  | r94 : Fig7 (m 4 * NKw) (NKw * m 4)
  | r95 : Fig7 (m0 * m 4) (m 4 * m0)
  | r96 : Fig7 (NKw * Kq 4 5 6 7) (Kq 4 5 6 7 * NKw)
  | r97 : Fig7 (T 0 * NKw) (NKw * Xab 1 3 * m 1 * m 3)
  | r98 : Fig7 (T 1 * NKw) (m0 * NKw * m0 * NKw * m0)
  | r99 : Fig7 (T 2 * NKw) (NKw * Xab 1 3)
  | r100 : Fig7 (NKw * Kq 1 3 4 5) (Kq 2 3 4 5 * Kq 0 1 2 4)
  | r101 : Fig7 (m0 * m 4 * Xab 0 4 * Ω * Xab 0 4 * m 4 * m0) Ω

/-! ## Figure 8 -/

/-- Figure 8, at every level from `2`. -/
inductive Fig8 : WRel (Gate (k + 2))
  | r102 : Fig8 (H2 * X0) (X0 * H2)
  | r103 : Fig8 (H2 * CX01) (CX01 * H2)
  | r104 : Fig8 (H2 * CCX12) (K01 * K12 * CCZw * K12 * K01 * H2)
  | r105 : Fig8 (H2 * CCZw) (CCX01 * H2)
  | r106 : Fig8 (H2 * K12) (K12 * H2)
  | r107 : Fig8 (H2 * NKw) (NKw * H2)
  | r108 : Fig8 (H2 * H2) 1

/-! ## The relation `r_K` of Section 5.5, missing from `R₁` -/

/-- `r_K`: `K₁₂ = X₀ K_[0,1,2,3] X₀ K_[0,1,2,3]`. -/
inductive RK : WRel (Gate (k + 1))
  | rK : RK K12 (X0 * NKw * X0 * NKw)

/-! ## The presentations -/

/-- `R₁ = R₀ ∪ R₈₄` (Theorem 5.2 as printed). -/
inductive R1 : WRel G₁
  | fig4 {w v : Word G₁} : R0 w v → R1 w v
  | fig7 {w v : Word G₁} : Fig7 w v → R1 w v

/-- `R₁⁺ = R₁ ∪ {r_K}`. -/
inductive R1plus : WRel G₁
  | fig4 {w v : Word G₁} : R0 w v → R1plus w v
  | fig7 {w v : Word G₁} : Fig7 w v → R1plus w v
  | rK {w v : Word G₁} : RK w v → R1plus w v

/-- `R₂ = R₁ ∪ Figure 8` (Theorem 6.3 as printed). -/
inductive R2 : WRel G₂
  | fig4 {w v : Word G₂} : R0 w v → R2 w v
  | fig7 {w v : Word G₂} : Fig7 w v → R2 w v
  | fig8 {w v : Word G₂} : Fig8 w v → R2 w v

/-- `R₂⁺ = R₂ ∪ {r_K}`. -/
inductive R2plus : WRel G₂
  | fig4 {w v : Word G₂} : R0 w v → R2plus w v
  | fig7 {w v : Word G₂} : Fig7 w v → R2plus w v
  | fig8 {w v : Word G₂} : Fig8 w v → R2plus w v
  | rK {w v : Word G₂} : RK w v → R2plus w v

end QCert.ToffoliHadamardRS
