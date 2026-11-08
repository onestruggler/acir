/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the gates

Translation of `Examples/Groups/CCX+H-3qubit-RS/Gates.agda`.

The gates of Amy, Ross and Wesley, "A Sound and Complete Equational Theory
for 3-Qubit Toffoli-Hadamard Circuits" (QPL 2024, arXiv:2407.11152), by the
level at which they enter:

* level 0, the Toffoli-K gates `𝒟` of Section 4.1: `X_j`, `Z_j`, `CX_{j,k}`,
  `CZ_{j,k}`, `CCX_{j,k}`, `K_{0,1}`, `K_{1,2}` and the swaps `σ_{j,k}`
  (written `SW` here);
* level 1, `Σ₁ = 𝒟 ∪ {K_[0,1,2,3], CCZ}` of Section 5.6 (`NK` is the paper's
  `K_[0,1,2,3]`, the `K₁₂` gate controlled negatively by qubit 0);
* level 2, `Σ₂ = Σ₁ ∪ {H₂}` of Section 6.

A gate of level `k` is a letter of `Gate k'` for every `k' ≥ k`, so the
letters keep their names across the three alphabets.  Qubit 0 is the most
significant: basis state `|x₀x₁x₂⟩` is index `4x₀ + 2x₁ + x₂`.  `CX_{j,k}`
has control `j` and target `k`, `CCX_{j,k}` has controls `j` and `k`, and
words are in operator order (the rightmost letter acts first).
-/
import QCert.Presentation

namespace QCert.ToffoliHadamardRS

/-! ## Letters -/

/-- The letters, indexed by the level. -/
inductive Gate : ℕ → Type
  | X₀ {k : ℕ} : Gate k
  | X₁ {k : ℕ} : Gate k
  | X₂ {k : ℕ} : Gate k
  | Z₀ {k : ℕ} : Gate k
  | Z₁ {k : ℕ} : Gate k
  | Z₂ {k : ℕ} : Gate k
  | CX₀₁ {k : ℕ} : Gate k
  | CX₀₂ {k : ℕ} : Gate k
  | CX₁₀ {k : ℕ} : Gate k
  | CX₁₂ {k : ℕ} : Gate k
  | CX₂₀ {k : ℕ} : Gate k
  | CX₂₁ {k : ℕ} : Gate k
  | CZ₀₁ {k : ℕ} : Gate k
  | CZ₀₂ {k : ℕ} : Gate k
  | CZ₁₂ {k : ℕ} : Gate k
  | CCX₀₁ {k : ℕ} : Gate k
  | CCX₀₂ {k : ℕ} : Gate k
  | CCX₁₂ {k : ℕ} : Gate k
  | K₀₁ {k : ℕ} : Gate k
  | K₁₂ {k : ℕ} : Gate k
  | SW₀₁ {k : ℕ} : Gate k
  | SW₀₂ {k : ℕ} : Gate k
  | SW₁₂ {k : ℕ} : Gate k
  | NK {k : ℕ} : Gate (k + 1)
  | CCZ {k : ℕ} : Gate (k + 1)
  | H₂ {k : ℕ} : Gate (k + 2)

/-- Toffoli-K circuits, circuits over `Σ₁` and over `Σ₂`. -/
abbrev GD := Gate 0
abbrev G₁ := Gate 1
abbrev G₂ := Gate 2

variable {k : ℕ}

namespace Gate

/-- A letter of one level is a letter of the next. -/
def up : Gate k → Gate (k + 1)
  | X₀ => X₀
  | X₁ => X₁
  | X₂ => X₂
  | Z₀ => Z₀
  | Z₁ => Z₁
  | Z₂ => Z₂
  | CX₀₁ => CX₀₁
  | CX₀₂ => CX₀₂
  | CX₁₀ => CX₁₀
  | CX₁₂ => CX₁₂
  | CX₂₀ => CX₂₀
  | CX₂₁ => CX₂₁
  | CZ₀₁ => CZ₀₁
  | CZ₀₂ => CZ₀₂
  | CZ₁₂ => CZ₁₂
  | CCX₀₁ => CCX₀₁
  | CCX₀₂ => CCX₀₂
  | CCX₁₂ => CCX₁₂
  | K₀₁ => K₀₁
  | K₁₂ => K₁₂
  | SW₀₁ => SW₀₁
  | SW₀₂ => SW₀₂
  | SW₁₂ => SW₁₂
  | NK => NK
  | CCZ => CCZ
  | H₂ => H₂

/-! ## Codes -/

/-- An injective code, for comparing letters by computation. -/
def code : Gate k → ℕ
  | X₀ => 0
  | X₁ => 1
  | X₂ => 2
  | Z₀ => 3
  | Z₁ => 4
  | Z₂ => 5
  | CX₀₁ => 6
  | CX₀₂ => 7
  | CX₁₀ => 8
  | CX₁₂ => 9
  | CX₂₀ => 10
  | CX₂₁ => 11
  | CZ₀₁ => 12
  | CZ₀₂ => 13
  | CZ₁₂ => 14
  | CCX₀₁ => 15
  | CCX₀₂ => 16
  | CCX₁₂ => 17
  | K₀₁ => 18
  | K₁₂ => 19
  | SW₀₁ => 20
  | SW₀₂ => 21
  | SW₁₂ => 22
  | NK => 23
  | CCZ => 24
  | H₂ => 25

/-- The letters of the levels above `1` and `2`. -/
def decode' : (k : ℕ) → ℕ → Gate k
  | _, 0 => SW₀₁
  | _, 1 => SW₀₂
  | _, 2 => SW₁₂
  | _ + 1, 3 => NK
  | _ + 1, 4 => CCZ
  | _ + 2, 5 => H₂
  | _, _ => X₀

/-- The inverse of `code`. -/
def decode (k : ℕ) : ℕ → Gate k
  | 0 => X₀
  | 1 => X₁
  | 2 => X₂
  | 3 => Z₀
  | 4 => Z₁
  | 5 => Z₂
  | 6 => CX₀₁
  | 7 => CX₀₂
  | 8 => CX₁₀
  | 9 => CX₁₂
  | 10 => CX₂₀
  | 11 => CX₂₁
  | 12 => CZ₀₁
  | 13 => CZ₀₂
  | 14 => CZ₁₂
  | 15 => CCX₀₁
  | 16 => CCX₀₂
  | 17 => CCX₁₂
  | 18 => K₀₁
  | 19 => K₁₂
  | n => decode' k (n - 20)

theorem decode_code (g : Gate k) : decode k (code g) = g := by
  cases g <;> rfl

theorem code_inj {x y : Gate k} (e : code x = code y) : x = y := by
  rw [← decode_code x, ← decode_code y, e]

end Gate

/-- Letters with an injective code into `ℕ`, compared by computation. -/
class Coded (A : Type) where
  code : A → ℕ
  inj : ∀ {x y : A}, code x = code y → x = y

instance : Coded (Gate k) := ⟨Gate.code, Gate.code_inj⟩

open Gate

/-! ## One-letter words -/

abbrev X0 : Word (Gate k) := FreeMonoid.of X₀
abbrev X1 : Word (Gate k) := FreeMonoid.of X₁
abbrev X2 : Word (Gate k) := FreeMonoid.of X₂
abbrev Z0 : Word (Gate k) := FreeMonoid.of Z₀
abbrev Z1 : Word (Gate k) := FreeMonoid.of Z₁
abbrev Z2 : Word (Gate k) := FreeMonoid.of Z₂
abbrev CX01 : Word (Gate k) := FreeMonoid.of CX₀₁
abbrev CX02 : Word (Gate k) := FreeMonoid.of CX₀₂
abbrev CX10 : Word (Gate k) := FreeMonoid.of CX₁₀
abbrev CX12 : Word (Gate k) := FreeMonoid.of CX₁₂
abbrev CX20 : Word (Gate k) := FreeMonoid.of CX₂₀
abbrev CX21 : Word (Gate k) := FreeMonoid.of CX₂₁
abbrev CZ01 : Word (Gate k) := FreeMonoid.of CZ₀₁
abbrev CZ02 : Word (Gate k) := FreeMonoid.of CZ₀₂
abbrev CZ12 : Word (Gate k) := FreeMonoid.of CZ₁₂
abbrev CCX01 : Word (Gate k) := FreeMonoid.of CCX₀₁
abbrev CCX02 : Word (Gate k) := FreeMonoid.of CCX₀₂
abbrev CCX12 : Word (Gate k) := FreeMonoid.of CCX₁₂
abbrev K01 : Word (Gate k) := FreeMonoid.of K₀₁
abbrev K12 : Word (Gate k) := FreeMonoid.of K₁₂
abbrev SW01 : Word (Gate k) := FreeMonoid.of SW₀₁
abbrev SW02 : Word (Gate k) := FreeMonoid.of SW₀₂
abbrev SW12 : Word (Gate k) := FreeMonoid.of SW₁₂

abbrev NKw : Word (Gate (k + 1)) := FreeMonoid.of NK
abbrev CCZw : Word (Gate (k + 1)) := FreeMonoid.of CCZ

abbrev H2 : Word (Gate (k + 2)) := FreeMonoid.of H₂

/-- A word of one level as a word of the next. -/
abbrev upW : Word (Gate k) →* Word (Gate (k + 1)) := FreeMonoid.map Gate.up

end QCert.ToffoliHadamardRS
