/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the generators and relations of `Uₙ(ℤ[1/2, i])`

X. Bian and P. Selinger, *Generators and relations for `Uₙ(ℤ[1/2, i])`*,
QPL 2021 (EPTCS 343), arXiv:2105.14047.

The generators (§3.1) are the one- and two-level matrices of types `X`, `K`
and `i`: `X_[j,k]` and `K_[j,k]` for `0 ≤ j < k < n`, and `i_[j]` for
`0 ≤ j < n`.  Indices start at `0`, as in the paper.  The relations are
those of Figure 1, numbered (1)–(19) as printed; in each, the indices are
distinct and every generator `X_[a,b]`, `K_[a,b]` has `a < b` (the
caption's convention, which here is part of each constructor).

A word `x₁ x₂ ⋯ xₘ` denotes the matrix product `x₁ x₂ ⋯ xₘ` (§2.4).
-/
import QCert.Presentation

namespace QCert.BianSelingerUn

/-- The generators `𝒢` of §3.1. -/
inductive Gen (n : ℕ) : Type
  /-- `X_[j,k]`, `j < k`: the two-level matrix of type `X`. -/
  | X (j k : Fin n) (h : j < k)
  /-- `K_[j,k]`, `j < k`: the two-level matrix of type `K = ω† H`. -/
  | K (j k : Fin n) (h : j < k)
  /-- `i_[j]`: the one-level matrix of type `i`. -/
  | i (j : Fin n)
  deriving DecidableEq

variable {n : ℕ}

/-- `X_[j,k]` as a word. -/
abbrev X (j k : Fin n) (h : j < k) : Word (Gen n) := FreeMonoid.of (Gen.X j k h)
/-- `K_[j,k]` as a word. -/
abbrev K (j k : Fin n) (h : j < k) : Word (Gen n) := FreeMonoid.of (Gen.K j k h)
/-- `i_[j]` as a word. -/
abbrev i (j : Fin n) : Word (Gen n) := FreeMonoid.of (Gen.i j)

/-- The relations `ℛ` of Figure 1. -/
inductive Rel (n : ℕ) : WRel (Gen n)
  /-- (1) `i_[j]⁴ ∼ ε`. -/
  | r1 (j : Fin n) : Rel n (i j ^ 4) 1
  /-- (2) `X_[j,k]² ∼ ε`. -/
  | r2 (j k : Fin n) (hjk : j < k) : Rel n (X j k hjk ^ 2) 1
  /-- (3) `K_[j,k]⁸ ∼ ε`. -/
  | r3 (j k : Fin n) (hjk : j < k) : Rel n (K j k hjk ^ 8) 1
  /-- (4) `i_[j] i_[k] ∼ i_[k] i_[j]`. -/
  | r4 (j k : Fin n) (hjk : j ≠ k) : Rel n (i j * i k) (i k * i j)
  /-- (5) `i_[j] X_[k,ℓ] ∼ X_[k,ℓ] i_[j]`. -/
  | r5 (j k l : Fin n) (hkl : k < l) (hjk : j ≠ k) (hjl : j ≠ l) :
      Rel n (i j * X k l hkl) (X k l hkl * i j)
  /-- (6) `i_[j] K_[k,ℓ] ∼ K_[k,ℓ] i_[j]`. -/
  | r6 (j k l : Fin n) (hkl : k < l) (hjk : j ≠ k) (hjl : j ≠ l) :
      Rel n (i j * K k l hkl) (K k l hkl * i j)
  /-- (7) `X_[j,k] X_[ℓ,m] ∼ X_[ℓ,m] X_[j,k]`. -/
  | r7 (j k l m : Fin n) (hjk : j < k) (hlm : l < m)
      (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
      Rel n (X j k hjk * X l m hlm) (X l m hlm * X j k hjk)
  /-- (8) `X_[j,k] K_[ℓ,m] ∼ K_[ℓ,m] X_[j,k]`. -/
  | r8 (j k l m : Fin n) (hjk : j < k) (hlm : l < m)
      (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
      Rel n (X j k hjk * K l m hlm) (K l m hlm * X j k hjk)
  /-- (9) `K_[j,k] K_[ℓ,m] ∼ K_[ℓ,m] K_[j,k]`. -/
  | r9 (j k l m : Fin n) (hjk : j < k) (hlm : l < m)
      (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m) :
      Rel n (K j k hjk * K l m hlm) (K l m hlm * K j k hjk)
  /-- (10) `i_[k] X_[j,k] ∼ X_[j,k] i_[j]`. -/
  | r10 (j k : Fin n) (hjk : j < k) : Rel n (i k * X j k hjk) (X j k hjk * i j)
  /-- (11) `X_[k,ℓ] X_[j,k] ∼ X_[j,k] X_[j,ℓ]`. -/
  | r11 (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
      Rel n (X k l hkl * X j k hjk) (X j k hjk * X j l (hjk.trans hkl))
  /-- (12) `X_[j,ℓ] X_[k,ℓ] ∼ X_[k,ℓ] X_[j,k]`. -/
  | r12 (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
      Rel n (X j l (hjk.trans hkl) * X k l hkl) (X k l hkl * X j k hjk)
  /-- (13) `K_[k,ℓ] X_[j,k] ∼ X_[j,k] K_[j,ℓ]`. -/
  | r13 (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
      Rel n (K k l hkl * X j k hjk) (X j k hjk * K j l (hjk.trans hkl))
  /-- (14) `K_[j,ℓ] X_[k,ℓ] ∼ X_[k,ℓ] K_[j,k]`. -/
  | r14 (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
      Rel n (K j l (hjk.trans hkl) * X k l hkl) (X k l hkl * K j k hjk)
  /-- (15) `K_[j,k] i_[k]² ∼ X_[j,k] K_[j,k]`. -/
  | r15 (j k : Fin n) (hjk : j < k) : Rel n (K j k hjk * i k ^ 2) (X j k hjk * K j k hjk)
  /-- (16) `K_[j,k] i_[k]³ ∼ i_[k] K_[j,k] i_[k] K_[j,k]`. -/
  | r16 (j k : Fin n) (hjk : j < k) :
      Rel n (K j k hjk * i k ^ 3) (i k * K j k hjk * i k * K j k hjk)
  /-- (17) `K_[j,k] i_[j] i_[k] ∼ i_[j] i_[k] K_[j,k]`. -/
  | r17 (j k : Fin n) (hjk : j < k) :
      Rel n (K j k hjk * i j * i k) (i j * i k * K j k hjk)
  /-- (18) `K_[j,k]² i_[j] i_[k] ∼ ε`. -/
  | r18 (j k : Fin n) (hjk : j < k) : Rel n (K j k hjk ^ 2 * i j * i k) 1
  /-- (19) `K_[j,k] K_[ℓ,m] K_[j,ℓ] K_[k,m] ∼ K_[j,ℓ] K_[k,m] K_[j,k] K_[ℓ,m]`
  (`j, k, ℓ, m` distinct; with the order conditions `j < k`, `ℓ < m`, `j < ℓ`,
  `k < m` of the four generators, that is `k ≠ ℓ`). -/
  | r19 (j k l m : Fin n) (hjk : j < k) (hlm : l < m) (hjl : j < l) (hkm : k < m)
      (hkl : k ≠ l) :
      Rel n (K j k hjk * K l m hlm * K j l hjl * K k m hkm)
        (K j l hjl * K k m hkm * K j k hjk * K l m hlm)

end QCert.BianSelingerUn
