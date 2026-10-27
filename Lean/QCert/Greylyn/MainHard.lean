/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: Subcases 4.3 and 4.4 of the Main Lemma

The one configuration of the basic edge `X_[a,a+1]` that the thesis treats
separately: the pivot column has the odd entries `α < a` as its first two
and `a + 1` is odd too.  With `n ≤ 4` this forces `n = 4`, `α = 0`, `a = 1`,
pivot `3` and all four entries odd.
-/
import QCert.Greylyn.MainH

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

/-- Subcases 4.3 and 4.4 of the proof of Lemma 31. -/
theorem square_X_hard (hn : n ≤ 4) {s : St n} (hs : s ≠ 1) {a b : Fin n} (hab : a < b)
    (hb : (b : ℕ) = a + 1) {p : Fin n} (hp : IsPivot s p) (hbp : b ≤ p) {u : Fin n → ZOmega}
    (hu : HasNum (col s p) (lde (col s p)) u) (hk : 0 < lde (col s p)) {α : Fin n}
    (hf : FirstTwo u α a) (hob : IsOdd (u b)) : Square s (Gen.X a b hab) := by
  sorry

end

end QCert.Greylyn
