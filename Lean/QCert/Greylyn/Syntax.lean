/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the generators and relations of `Uₙ(ℤ[1/√2, i])`

S. E. M. Greylyn, *Generators and relations for the group
`U₄(ℤ[1/√2, i])`*, M.Sc. thesis, Dalhousie University, 2014,
arXiv:1408.6204.

The generating set `(*)` (Definition 6) consists of the one- and two-level
matrices `X_[α,β]`, `H_[α,β]` (`α < β`) and `ω_[α]`.  The thesis numbers
indices from `1` to `n`; here they are `Fin n`, from `0` to `n - 1`.  The
relations are those of Table 3.1, numbered (1)–(20) as printed, each with
its side conditions.

A word `G_q ⋯ G₁` denotes the matrix product `G_q ⋯ G₁` (Definition 20), so
a word written left to right denotes the product in the same order.
-/
import QCert.Presentation

namespace QCert.Greylyn

/-- The generating set `(*)` of Definition 6. -/
inductive Gen (n : ℕ) : Type
  /-- `X_[j,k]`, `j < k`: the two-level matrix of type `X`. -/
  | X (j k : Fin n) (h : j < k)
  /-- `H_[j,k]`, `j < k`: the two-level matrix of type `H`. -/
  | H (j k : Fin n) (h : j < k)
  /-- `ω_[j]`: the one-level matrix of type `ω = e^{iπ/4}`. -/
  | ω (j : Fin n)
  deriving DecidableEq

variable {n : ℕ}

/-- `X_[j,k]` as a word. -/
abbrev X (j k : Fin n) (h : j < k) : Word (Gen n) := FreeMonoid.of (Gen.X j k h)
/-- `H_[j,k]` as a word. -/
abbrev H (j k : Fin n) (h : j < k) : Word (Gen n) := FreeMonoid.of (Gen.H j k h)
/-- `ω_[j]` as a word. -/
abbrev ω (j : Fin n) : Word (Gen n) := FreeMonoid.of (Gen.ω j)

/-- The equations `≈` of Table 3.1. -/
inductive Rel (n : ℕ) : WRel (Gen n)
  /-- (1) `ω_[j]⁸ ≈ ε`. -/
  | r1 (j : Fin n) : Rel n (ω j ^ 8) 1
  /-- (2) `H_[j,k]² ≈ ε` (`j < k`). -/
  | r2 (j k : Fin n) (hjk : j < k) : Rel n (H j k hjk ^ 2) 1
  /-- (3) `X_[j,k]² ≈ ε` (`j < k`). -/
  | r3 (j k : Fin n) (hjk : j < k) : Rel n (X j k hjk ^ 2) 1
  /-- (4) `ω_[j] ω_[k] ≈ ω_[k] ω_[j]` (`j ≠ k`). -/
  | r4 (j k : Fin n) (hjk : j ≠ k) : Rel n (ω j * ω k) (ω k * ω j)
  /-- (5) `ω_[ℓ] H_[j,k] ≈ H_[j,k] ω_[ℓ]` (`j < k`, `ℓ ≠ j, k`). -/
  | r5 (j k l : Fin n) (hjk : j < k) (hlj : l ≠ j) (hlk : l ≠ k) :
      Rel n (ω l * H j k hjk) (H j k hjk * ω l)
  /-- (6) `ω_[ℓ] X_[j,k] ≈ X_[j,k] ω_[ℓ]` (`j < k`, `ℓ ≠ j, k`). -/
  | r6 (j k l : Fin n) (hjk : j < k) (hlj : l ≠ j) (hlk : l ≠ k) :
      Rel n (ω l * X j k hjk) (X j k hjk * ω l)
  /-- (7) `H_[j,k] H_[ℓ,t] ≈ H_[ℓ,t] H_[j,k]` (`j < k`, `ℓ < t`,
  `{ℓ, t} ∩ {j, k} = ∅`). -/
  | r7 (j k l t : Fin n) (hjk : j < k) (hlt : l < t)
      (hlj : l ≠ j) (hlk : l ≠ k) (htj : t ≠ j) (htk : t ≠ k) :
      Rel n (H j k hjk * H l t hlt) (H l t hlt * H j k hjk)
  /-- (8) `H_[j,k] X_[ℓ,t] ≈ X_[ℓ,t] H_[j,k]` (`j < k`, `ℓ < t`,
  `{ℓ, t} ∩ {j, k} = ∅`). -/
  | r8 (j k l t : Fin n) (hjk : j < k) (hlt : l < t)
      (hlj : l ≠ j) (hlk : l ≠ k) (htj : t ≠ j) (htk : t ≠ k) :
      Rel n (H j k hjk * X l t hlt) (X l t hlt * H j k hjk)
  /-- (9) `X_[j,k] X_[ℓ,t] ≈ X_[ℓ,t] X_[j,k]` (`j < k`, `ℓ < t`,
  `{ℓ, t} ∩ {j, k} = ∅`). -/
  | r9 (j k l t : Fin n) (hjk : j < k) (hlt : l < t)
      (hlj : l ≠ j) (hlk : l ≠ k) (htj : t ≠ j) (htk : t ≠ k) :
      Rel n (X j k hjk * X l t hlt) (X l t hlt * X j k hjk)
  /-- (10) `X_[j,k] ω_[k] ≈ ω_[j] X_[j,k]` (`j < k`). -/
  | r10 (j k : Fin n) (hjk : j < k) : Rel n (X j k hjk * ω k) (ω j * X j k hjk)
  /-- (11) `X_[j,k] ω_[j] ≈ ω_[k] X_[j,k]` (`j < k`). -/
  | r11 (j k : Fin n) (hjk : j < k) : Rel n (X j k hjk * ω j) (ω k * X j k hjk)
  /-- (12) `X_[j,k] X_[j,ℓ] ≈ X_[k,ℓ] X_[j,k]` (`j < k < ℓ`). -/
  | r12 (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
      Rel n (X j k hjk * X j l (hjk.trans hkl)) (X k l hkl * X j k hjk)
  /-- (13) `X_[j,k] X_[ℓ,j] ≈ X_[ℓ,k] X_[j,k]` (`ℓ < j < k`). -/
  | r13 (j k l : Fin n) (hlj : l < j) (hjk : j < k) :
      Rel n (X j k hjk * X l j hlj) (X l k (hlj.trans hjk) * X j k hjk)
  /-- (14) `X_[j,k] H_[j,ℓ] ≈ H_[k,ℓ] X_[j,k]` (`j < k < ℓ`). -/
  | r14 (j k l : Fin n) (hjk : j < k) (hkl : k < l) :
      Rel n (X j k hjk * H j l (hjk.trans hkl)) (H k l hkl * X j k hjk)
  /-- (15) `X_[j,k] H_[ℓ,j] ≈ H_[ℓ,k] X_[j,k]` (`ℓ < j < k`). -/
  | r15 (j k l : Fin n) (hlj : l < j) (hjk : j < k) :
      Rel n (X j k hjk * H l j hlj) (H l k (hlj.trans hjk) * X j k hjk)
  /-- (16) `ω_[j] ω_[k] X_[j,k] ≈ X_[j,k] ω_[j] ω_[k]` (`j < k`). -/
  | r16 (j k : Fin n) (hjk : j < k) :
      Rel n (ω j * ω k * X j k hjk) (X j k hjk * ω j * ω k)
  /-- (17) `ω_[j] ω_[k] H_[j,k] ≈ H_[j,k] ω_[j] ω_[k]` (`j < k`). -/
  | r17 (j k : Fin n) (hjk : j < k) :
      Rel n (ω j * ω k * H j k hjk) (H j k hjk * ω j * ω k)
  /-- (18) `H_[j,k] X_[j,k] ≈ ω⁴_[k] H_[j,k]` (`j < k`). -/
  | r18 (j k : Fin n) (hjk : j < k) : Rel n (H j k hjk * X j k hjk) (ω k ^ 4 * H j k hjk)
  /-- (19) `H_[j,k] ω²_[j] H_[j,k] ≈ ω⁶_[j] H_[j,k] ω³_[j] ω⁵_[k]` (`j < k`). -/
  | r19 (j k : Fin n) (hjk : j < k) :
      Rel n (H j k hjk * ω j ^ 2 * H j k hjk) (ω j ^ 6 * H j k hjk * ω j ^ 3 * ω k ^ 5)
  /-- (20) `H_[j,k] H_[ℓ,t] H_[j,ℓ] H_[k,t] ≈ H_[j,ℓ] H_[k,t] H_[j,k] H_[ℓ,t]`
  (`j < k < ℓ < t`). -/
  | r20 (j k l t : Fin n) (hjk : j < k) (hkl : k < l) (hlt : l < t) :
      Rel n (H j k hjk * H l t hlt * H j l (hjk.trans hkl) * H k t (hkl.trans hlt))
        (H j l (hjk.trans hkl) * H k t (hkl.trans hlt) * H j k hjk * H l t hlt)

end QCert.Greylyn
