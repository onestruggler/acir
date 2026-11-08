/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the encoding

Translation of `Encoding.agda`.  Every gate written as a word over the
one-, two- and four-level generators of Li, Ross and Selinger
(`QCert.LiRossSelinger`), at `n = 8`:

* a permutation gate is the product of the transpositions `X_[a,b]` of the
  basis states it exchanges, a diagonal gate the product of the `(-1)_[a]`
  it negates, `K₁₂ = K_[0,1,2,3] K_[4,5,6,7]` and `K₀₁ = K_[0,2,4,6]
  K_[1,3,5,7]` (`H ⊗ H` on the pairs of qubits, the other one fixed),
  `K_[0,1,2,3]` itself, `CCZ = (-1)_[7]`, and `H₂` the global generator
  `I ⊗ H` of §5 of Li–Ross–Selinger.

These words are the semantics: a circuit denotes the matrix of its encoding
(`Semantics`), and that each gate's matrix is the expected one is checked
entry by entry (`GateMatrices`).  Li–Ross–Selinger's indices start at `0`.
-/
import QCert.ToffoliHadamardRS.Gates
import QCert.LiRossSelinger.Syntax

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen GenL)

/-! ## Two-level letters at literal indices

The order side conditions are found by evaluation (the Agda's `lt`). -/

/-- `(-1)_[a]`. -/
def mG (a : ℕ) (ha : a < 8 := by decide) : Gen 8 := .neg ⟨a, ha⟩

/-- `X_[a,b]`. -/
def xG (a b : ℕ) (hb : b < 8 := by decide) (h : a < b := by decide) : Gen 8 :=
  .x ⟨a, by omega⟩ ⟨b, hb⟩ (Fin.mk_lt_mk.2 h)

/-- `K_[a,b,c,d]`. -/
def kG (a b c d : ℕ) (hd : d < 8 := by decide) (h₁ : a < b := by decide) (h₂ : b < c := by decide)
    (h₃ : c < d := by decide) : Gen 8 :=
  .k ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩ (Fin.mk_lt_mk.2 h₁) (Fin.mk_lt_mk.2 h₂)
    (Fin.mk_lt_mk.2 h₃)

/-- `M[a]`, `X[a,b]`, `K[a,b,c,d]` as words. -/
abbrev Mw (a : ℕ) (ha : a < 8 := by decide) : Word (Gen 8) := FreeMonoid.of (mG a ha)

abbrev Xw (a b : ℕ) (hb : b < 8 := by decide) (h : a < b := by decide) : Word (Gen 8) :=
  FreeMonoid.of (xG a b hb h)

abbrev Kw (a b c d : ℕ) (hd : d < 8 := by decide) (h₁ : a < b := by decide)
    (h₂ : b < c := by decide) (h₃ : c < d := by decide) : Word (Gen 8) :=
  FreeMonoid.of (kG a b c d hd h₁ h₂ h₃)

/-! ## The encoding -/

variable {k : ℕ}

open Gate in
/-- The letters of `Σ₁`; `H₂`, which has no matrix over `𝔻`, is sent to `ε`
here and handled by `encL`. -/
def enc : Gate k → Word (Gen 8)
  | X₀ => Xw 0 4 * Xw 1 5 * Xw 2 6 * Xw 3 7
  | X₁ => Xw 0 2 * Xw 1 3 * Xw 4 6 * Xw 5 7
  | X₂ => Xw 0 1 * Xw 2 3 * Xw 4 5 * Xw 6 7
  | Z₀ => Mw 4 * Mw 5 * Mw 6 * Mw 7
  | Z₁ => Mw 2 * Mw 3 * Mw 6 * Mw 7
  | Z₂ => Mw 1 * Mw 3 * Mw 5 * Mw 7
  | CX₀₁ => Xw 4 6 * Xw 5 7
  | CX₀₂ => Xw 4 5 * Xw 6 7
  | CX₁₀ => Xw 2 6 * Xw 3 7
  | CX₁₂ => Xw 2 3 * Xw 6 7
  | CX₂₀ => Xw 1 5 * Xw 3 7
  | CX₂₁ => Xw 1 3 * Xw 5 7
  | CZ₀₁ => Mw 6 * Mw 7
  | CZ₀₂ => Mw 5 * Mw 7
  | CZ₁₂ => Mw 3 * Mw 7
  | CCX₀₁ => Xw 6 7
  | CCX₀₂ => Xw 5 7
  | CCX₁₂ => Xw 3 7
  | K₀₁ => Kw 0 2 4 6 * Kw 1 3 5 7
  | K₁₂ => Kw 0 1 2 3 * Kw 4 5 6 7
  | SW₀₁ => Xw 2 4 * Xw 3 5
  | SW₀₂ => Xw 1 4 * Xw 3 6
  | SW₁₂ => Xw 1 2 * Xw 5 6
  | NK => Kw 0 1 2 3
  | CCZ => Mw 7
  | H₂ => 1

/-- The letters of `Σ₂`. -/
def encL : Gate k → Word (GenL 4)
  | .H₂ => FreeMonoid.of .ih
  | g => LiRossSelinger.toL (enc g)

/-- On words. -/
abbrev encW : Word (Gate k) →* Word (Gen 8) := FreeMonoid.lift enc

abbrev encLW : Word (Gate k) →* Word (GenL 4) := FreeMonoid.lift encL

/-! ## The encodings as lists, for evaluation -/

/-- The letters of the encoding of a list of gates. -/
def encList : List (Gate k) → List (Gen 8) :=
  List.rec [] (fun g _ ih => (enc g).toList ++ ih)

def encLList : List (Gate k) → List (GenL 4) :=
  List.rec [] (fun g _ ih => (encL g).toList ++ ih)

theorem encW_toList (w : Word (Gate k)) : (encW w).toList = encList w.toList := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, FreeMonoid.toList_mul, ih, FreeMonoid.lift_eval_of]; rfl

theorem encLW_toList (w : Word (Gate k)) : (encLW w).toList = encLList w.toList := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, FreeMonoid.toList_mul, ih, FreeMonoid.lift_eval_of]; rfl

end QCert.ToffoliHadamardRS
