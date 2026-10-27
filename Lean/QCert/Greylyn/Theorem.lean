/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: a presentation of `Uₙ(ℤ[1/√2, i])` for `n ≤ 4`

Theorem 22 of S. E. M. Greylyn, *Generators and relations for the group
`U₄(ℤ[1/√2, i])`*, M.Sc. thesis, 2014, arXiv:1408.6204: the equations of
Table 3.1 are sound and complete for words over the generating set `(*)`,
which generates the group (Theorem 5, after Giles and Selinger).  The thesis
states the theorem for `n = 4`; its proof (the Main Lemma, Lemma 31) is for
states of dimension `n ≤ 4`, so the result holds for every `n ≤ 4`.
-/
import QCert.Greylyn.Semantics

namespace QCert.Greylyn

/-- Theorem 22 (with Theorem 5): for `n ≤ 4`, the generators `(*)` and the
equations of Table 3.1 present `Uₙ(ℤ[1/√2, i])`. -/
theorem presentation (n : ℕ) (hn : n ≤ 4) : IsPresentationOf (Rel n) (sem n) := by
  sorry

end QCert.Greylyn
