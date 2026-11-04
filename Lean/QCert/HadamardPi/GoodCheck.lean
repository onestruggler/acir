/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Good words decided on a pattern

`Good4 par w` (`Good.lean`) quantifies over the integer parameters of a window
of four odd numerators of one class.  On the pattern of `SymForms.lean` whose
forms are affine in the parameters `a₀, a₁, a₂, b₀, b₁, b₂, b₃, c, mm` (with
`a₃ = 2 mm + par − a₀ − a₁ − a₂`, `goodPat`) it is decided by evaluation
(`good4Chk`): the numerators after `w` at the old exponent are integral
(`allSome`) and one of them has every coefficient even.  `Switch.lean` proves
each of its `Good4` statements by `good4_of_chk (by decide +kernel)`.
-/
import QCert.HadamardPi.Good
import QCert.HadamardPi.SymForms

namespace QCert.HadamardPi

open Matrix FreeMonoid

noncomputable section

/-- The pattern of `Pat4` at the parity `par`, in the parameters
`a₀ a₁ a₂ b₀ b₁ b₂ b₃ c mm` (`a₃` eliminated). -/
def goodPat (par : ℤ) : List ZL :=
  [([1, 2, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0, 1, 0]),
    ([1, 0, 2, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2, 0, 0, 1, 0]),
    ([1, 0, 0, 2, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 2, 0, 1, 0]),
    ([2 * par + 1, -2, -2, -2, 0, 0, 0, 0, 0, 4], [0, 0, 0, 0, 0, 0, 0, 2, 1, 0])]

/-- The parameters of the pattern. -/
def goodPar (a b : Fin 4 → ℤ) (c mm : ℤ) : ℕ → ℤ
  | 0 => a 0
  | 1 => a 1
  | 2 => a 2
  | 3 => b 0
  | 4 => b 1
  | 5 => b 2
  | 6 => b 3
  | 7 => c
  | _ => mm

theorem pv_goodPat {a b : Fin 4 → ℤ} {c mm par : ℤ}
    (hsum : a 0 + a 1 + a 2 + a 3 = 2 * mm + par) :
    pv (goodPat par) (goodPar a b c mm) = Pat4 a b c := by
  funext j
  fin_cases j <;> ext <;> simp [pv, goodPat, zev, evv, c1, goodPar, Pat4] <;> omega

/-- The check: every numerator after `w` is integral at the old exponent, and
one of them is even for every value of the parameters. -/
def good4Chk (par : ℤ) (w : List (Gen 4)) : Bool :=
  allSome (goodPat par) w &&
    (List.range 4).any fun j => allEven ((divAll (goodPat par) w).getD j dZ).1

theorem good4_of_chk {par : ℤ} {w : List (Gen 4)} (h : good4Chk par w = true) : Good4 par w := by
  intro a b c mm hsum
  simp only [good4Chk, Bool.and_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨hall, j, hj, he⟩ := h
  refine ⟨fun j => zev ((divAll (goodPat par) w).getD j dZ) (goodPar a b c mm), fun j => ?_,
    ⟨j, hj⟩, ?_⟩
  · rw [← pv_goodPat hsum]
    exact divAll_sound hall _ j
  · exact not_odd_of_allEven he _

end

end QCert.HadamardPi
