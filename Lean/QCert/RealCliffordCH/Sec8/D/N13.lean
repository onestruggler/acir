/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.7 (Lemmas D.12–D.13): the interface of package (v)

The commutation properties of multi-controlled gates that Appendix E uses,
stated on `N` wires with completeness on fewer wires as a hypothesis, in
the conventions of `MC` (see `PLAN.md`).  In Lemma D.13 the controls `Λˣ`,
`Λʸ` are colourings `x`, `y` of the top wires `k, …, N - 1` (`colOn k N`),
the half-black dots of the figures are Boolean parameters `c₁, c₂, …`
(`ctlAt`), and "`x ≠ y`" is `DiffOn k N x y`.  Every statement here was
checked numerically against the definitions at `N = 3, …, 6` (scratch
`r87/iface.py`).  They are stated, not yet proved: package (v) of `PLAN.md`
replaces each `sorry` by its proof and keeps the statements.
-/
import QCert.RealCliffordCH.Sec8.D.N8

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

/-! ## Lemma D.12 -/

/-- (315): `X` on the box wire commutes with the box. -/
theorem eq315 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, Bx N]) (drawn [Bx N, xAt N 0]) := by
  sorry

/-- (316): `X` on the box wire commutes with the multi-controlled `H`. -/
theorem eq316 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (drawn [xAt N 0, mc N .hg [0, 1] (blackOn 2 N)])
      (drawn [mc N .hg [0, 1] (blackOn 2 N), xAt N 0]) := by
  sorry

/-- (317): the multi-controlled `ZX` and `XZ` are inverse. -/
theorem eq317 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x : ℕ → Bool) :
    Derivable (theory N) (drawn [mc N .zx [0] (colOn 1 N x), mc N .xz [0] (colOn 1 N x)]) 1 ∧
    Derivable (theory N) (drawn [mc N .xz [0] (colOn 1 N x), mc N .zx [0] (colOn 1 N x)]) 1 := by
  sorry

/-- (333): the multi-controlled `ZX` written with a multi-controlled `H`
(box wire 2, `H` on wire 0) and a box (box wire 1). -/
theorem eq333 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .zx [0] (blackOn 1 N))
      (drawn [mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N))]) := by
  sorry

/-- (334): the same for the multi-controlled `XZ`. -/
theorem eq334 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) :
    Derivable (theory N) (mc N .xz [0] (blackOn 1 N))
      (drawn [mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N)),
        mc N .box [1] (ctlOr (ctlAt 0 true) (blackOn 2 N)),
        mc N .hg [2, 0] (ctlOr (ctlAt 1 true) (blackOn 3 N))]) := by
  sorry

/-! ## Lemma D.13: commutations of coloured multi-controlled gates -/

/-- Two gates commute. -/
abbrev Comm (N : ℕ) (g₁ g₂ : Circ N) : Prop := Derivable (theory N) (drawn [g₁, g₂]) (drawn [g₂, g₁])

/-- (335) -/
theorem eq335 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N .box [0] (colOn 1 N y)) := by
  sorry

/-- (336) -/
theorem eq336 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N .box [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  sorry

/-- (337) -/
theorem eq337 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [0, 1] (colOn 2 N y)) := by
  sorry

/-- (338) -/
theorem eq338 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (c₁ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x))) (mc N .hg [1, 0] (colOn 2 N y)) := by
  sorry

/-- (339) -/
theorem eq339 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ c₃ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 N x))))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 N y))) := by
  sorry

/-- (340) -/
theorem eq340 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  sorry

/-- (342) -/
theorem eq342 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [0, 2] (ctlOr (ctlAt 1 c₂) (colOn 3 N y))) := by
  sorry

/-- (344) -/
theorem eq344 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (c₁ c₂ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N .hg [1, 2] (ctlOr (ctlAt 0 c₂) (colOn 3 N y))) := by
  sorry

/-- (345) -/
theorem eq345 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) :
    Comm N (mc N .hg [1, 0] (colOn 2 N x)) (mc N .hg [0, 1] (colOn 2 N y)) := by
  sorry

/-- (346) -/
theorem eq346 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (a : Bool) :
    Comm N (mc N .box [0] (colOn 1 N x)) (mc N (Kind.sgnZX a) [0] (colOn 1 N y)) := by
  sorry

/-- (347) -/
theorem eq347 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ c₂ : Bool) :
    Comm N (mc N .box [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  sorry

/-- (348) -/
theorem eq348 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N y))) := by
  sorry

/-- (349) -/
theorem eq349 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a c₁ : Bool) :
    Comm N (mc N .hg [0, 1] (colOn 2 N x))
      (mc N (Kind.sgnZX a) [1] (ctlOr (ctlAt 0 c₁) (colOn 2 N y))) := by
  sorry

/-- (350) -/
theorem eq350 (N : ℕ) (hN : 4 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 3 N x y)
    (a c₁ c₂ c₃ : Bool) :
    Comm N (mc N .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 N x)))
      (mc N (Kind.sgnZX a) [2] (ctlOr (ctlAt 1 c₂) (ctlOr (ctlAt 0 c₃) (colOn 3 N y)))) := by
  sorry

/-- (351) -/
theorem eq351 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (a b : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (colOn 1 N x)) (mc N (Kind.sgnZX b) [0] (colOn 1 N y)) := by
  sorry

/-- (352) -/
theorem eq352 (N : ℕ) (hN : 3 ≤ N) (ih : IH N) (x y : ℕ → Bool) (hxy : DiffOn 2 N x y)
    (a b c₁ c₂ : Bool) :
    Comm N (mc N (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 N x)))
      (mc N (Kind.sgnZX b) [1] (ctlOr (ctlAt 0 c₂) (colOn 2 N y))) := by
  sorry

end QCert.RealCliffordCH.Sec8.D
