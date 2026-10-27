/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: a presentation of `Uₙ(ℤ[1/2, i])`

Theorem 3.1 (Main theorem) of X. Bian and P. Selinger, *Generators and
relations for `Uₙ(ℤ[1/2, i])`*, QPL 2021, arXiv:2105.14047: for every `n`,
the one- and two-level matrices `X_[j,k]`, `K_[j,k]`, `i_[j]` (`Gen n`) and
the relations of Figure 1 (`Rel n`) present `Uₙ(ℤ[1/2, i])`, the group of
unitary `n × n` matrices with entries in `ℤ[1/2, i]`.
-/
import QCert.BianSelingerUn.Completeness
import QCert.Synthesis

namespace QCert.BianSelingerUn

/-- Theorem 3.1: `(𝒢, ℛ)` is a presentation of `Uₙ(ℤ[1/2, i])`. -/
theorem presentation (n : ℕ) : IsPresentationOf (Rel n) (sem n) :=
  normalWords.isPresentationOf grouplike (fun _ _ h => sound h)

end QCert.BianSelingerUn
