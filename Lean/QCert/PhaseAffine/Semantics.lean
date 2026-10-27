/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Prime-dimensional phase-affine circuits: semantics

The interpretation of Definitions 6 and 20 of Blake (arXiv:2603.06466): an
affine gate is the permutation `P_g : |x⟩ ↦ |g(x)⟩` of basis states, a phase
gate the diagonal `D_q : |x⟩ ↦ ω^{q(x)} |x⟩`, and `ω` the scalar `ω`:

* `X ↦ P_{x ↦ x + 1}`, `M_a ↦ P_{x ↦ a x}`;
* `CX ↦ P_{(x, y) ↦ (x, x + y)}`, `x` the label of the control (wire `1`) and
  `y` that of the target (wire `0`); `SWAP ↦ P_{(x, y) ↦ (y, x)}`;
* `ω ↦ ω`, `Z ↦ D_{x}`, `S ↦ D_{binom x 2}`, `T ↦ D_{binom x 3}`.

The paper works over `ℂ` with `ω = e^{2πi/d}`.  To stay exact, the matrices
are stated over any commutative ring `A` with an involution and an additive
character `ψ : 𝔽_d → A`, `ψ a` standing for `ω^a`, with `star (ψ a) =
ψ (-a)` (so that `ψ a` is unitary); completeness needs `ψ` injective (`ω`
primitive, Remark 2).  `ℂ` with `ZMod.stdAddChar` (`a ↦ e^{2πia/d}`) is the
paper's instance (`semℂ`).

A matrix is indexed by basis states `State d n` (a digit in `Fin d` on each
wire, read in `𝔽_d` through `ZMod.finEquiv`); the entry of `P_g D_q` in the
row of `|s⟩` and the column of `|t⟩` is `ψ (q t)` if `s = g t` and `0`
otherwise (`toOp`).
-/
import QCert.PhaseAffine.Syntax
import QCert.PhaseAffine.PhAff
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace QCert.PhaseAffine

/-- The pair `(g, q)` of each gate (Definitions 6 and 20). -/
def gateData (d lv : ℕ) : GateData (Gate d lv) d where
  scalar
    | .omega _ => 1
  gate1
    | .X => PA.perm fun v => v + 1
    | .M a => PA.perm fun v => (a : ZMod d) • v
    | .Z _ => PA.diag fun v => v 0
    | .S _ => PA.diag fun v => binom2 (v 0)
    | .T _ => PA.diag fun v => binom3 (v 0)
  gate2
    | .CX => PA.perm fun v => ![v 0 + v 1, v 1]
    | .SWAP => PA.perm fun v => ![v 1, v 0]
  gate3 g := nomatch g

theorem gateData_injective (d lv : ℕ) : (gateData d lv).Injective where
  gate1 g := by
    cases g with
    | X => intro v w h; simpa [gateData] using h
    | M a =>
      intro v w h
      have := congrArg (fun u => ((a⁻¹ : (ZMod d)ˣ) : ZMod d) • u) h
      simpa [gateData, smul_smul] using this
    | Z => exact fun _ _ h => h
    | S => exact fun _ _ h => h
    | T => exact fun _ _ h => h
  gate2 g := by
    cases g with
    | CX =>
      intro v w h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [gateData] at h0 h1
      funext i; fin_cases i
      · simpa [h1] using h0
      · exact h1
    | SWAP =>
      intro v w h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [gateData] at h0 h1
      funext i; fin_cases i
      · exact h1
      · exact h0
  gate3 g := nomatch g

section Matrices

variable {d : ℕ} [NeZero d] {A : Type*} [CommRing A] [StarRing A]

/-- The matrix semantics of the fragment of level `lv` over `A`, `ψ a`
standing for `ω^a`. -/
def sem (lv : ℕ) (ψ : AddChar (ZMod d) A) (hψ : ∀ a, star (ψ a) = ψ (-a)) :
    GateSem (Gate d lv) A d :=
  (gateData d lv).toGateSem ψ hψ (gateData_injective d lv)

/-- The matrix of a circuit is that of its pair `(g, q)`. -/
theorem sem_val (lv : ℕ) (ψ : AddChar (ZMod d) A) (hψ : ∀ a, star (ψ a) = ψ (-a)) {n : ℕ}
    (w : C d lv n) : ((sem lv ψ hψ).sem n w).1 = toOp ψ ((gateData d lv).sem n w) :=
  GateData.toGateSem_sem _ _ _ _ w

end Matrices

/-- `a ↦ e^{2πia/d}` satisfies `conj (ψ a) = ψ (-a)`. -/
theorem stdAddChar_star {d : ℕ} [NeZero d] (a : ZMod d) :
    star (ZMod.stdAddChar a) = ZMod.stdAddChar (-a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj, Complex.star_def]

/-- The paper's semantics: complex matrices with `ω = e^{2πi/d}`. -/
noncomputable def semℂ (d lv : ℕ) [NeZero d] : GateSem (Gate d lv) ℂ d :=
  sem lv ZMod.stdAddChar stdAddChar_star

end QCert.PhaseAffine
