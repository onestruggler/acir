/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Theorem 4.10 by the Reidemeister–Schreier theorem (Appendix A.3)

The data of Definition A.2, for the Reidemeister–Schreier theorem for
monoids (`QCert.reidemeister_schreier`, Theorem 4.3 of Bian–Selinger):

* `Y = 𝒢_N` (Hadamard-Π's generators, `QCert.HadamardPi.Gen`, two-level
  generators on increasing indices) with the relations of its Figure 6,
  complete by `QCert.HadamardPi.theorem_4_14`;
* `X = 𝒫_N` with the relations of Figure 8;
* the cosets `C = {ε, (-1)[1], H[0,1], H[0,1](-1)[1]}` (`Cos`) of the subgroup
  of matrices with even `H`- and `ZX`-parities, `ε` distinguished;
* `f = σ` (`sigmaG`): a letter of `𝒫_N` as the word of its two factors, a
  factor on decreasing indices written `X_[b,a]` or `X_[b,a] H_[b,a] X_[b,a]`
  (Equations (e1), (e2));
* `h = τ` (`tauA`), the coset action of Definition A.2: `⟦c g⟧ = ⟦p c'⟧`
  for `(p, c') = τ(c, g)` (checked numerically for every case at `N = 8`).
  In Definition A.2 `a + b` is the one of `a, b` that is not `0` and `ab` the
  one that is not `1` (`notZero`, `notOne`).

Hypothesis (a) of the theorem is `ItemA` (the equations (DE-ZZ), …, (DE-HH)
of Appendix A.3.2) and hypothesis (b) is `ItemB` (one equation per relation
of Figure 6 and coset).  Claim A is needed only for proper words, since
Theorem 4.10 is about proper words (`claimA_proper`).  σ preserves the
semantics (`sigma_sem`), so two proper words with the same matrix have
σ-images equal by Figure 6, and `thm410_of` concludes.
-/
import QCert.RealCliffordCH.Sec8.A.Fig10b
import QCert.RealCliffordCH.Sec8.Statement
import QCert.CliffordT2.ReidemeisterSchreier
import QCert.HadamardPi.Theorem

namespace QCert.RealCliffordCH.Sec8

open Matrix

/-! ## The cosets and the coset action (Definition A.2) -/

/-- The cosets `ε, (-1)[1], H[0,1], H[0,1](-1)[1]`. -/
inductive Cos
  | e
  | z
  | h
  | hz
  deriving DecidableEq

variable (n : ℕ)

/-- The index `0`. -/
abbrev o0 : Fin (2 ^ n) := ix n 0

/-- The index `1`. -/
abbrev o1 : Fin (2 ^ n) := ix n 1

/-- `ab`: of two indices, the one that is not `1`. -/
def notOne (a b : Fin (2 ^ n)) : Fin (2 ^ n) := if (a : ℕ) = 1 then b else a

/-- `a + b`: of two indices, the one that is not `0`. -/
def notZero (a b : Fin (2 ^ n)) : Fin (2 ^ n) := if (a : ℕ) = 0 then b else a

/-- `τ(c, X[a,b])` for `c = H[0,1]` (`isH`) and `c = H[0,1](-1)[1]`, `a < b`. -/
def tauX (isH : Bool) (a b : Fin (2 ^ n)) : Word (PG (2 ^ n)) :=
  if (a : ℕ) = 0 ∧ (b : ℕ) = 1 then
    FreeMonoid.of (.zx (if isH then o1 n else o0 n) (o0 n) (o1 n))
  else if (a : ℕ) = 0 then
    FreeMonoid.of (.xx (o0 n) (o1 n) a b) * FreeMonoid.of (.hh (notZero n a b) (o1 n) (o0 n) (o1 n))
  else if (a : ℕ) = 1 then
    (if isH then FreeMonoid.of (.zx (notOne n a b) a b) else FreeMonoid.of (.xx (o0 n) (o1 n) a b)) *
      FreeMonoid.of (.hh (o0 n) (notOne n a b) (o0 n) (o1 n))
  else FreeMonoid.of (.xx a b (o0 n) (o1 n))

/-- `τ(c, (-1)[a])` for `c = H[0,1]` and `c = H[0,1](-1)[1]`. -/
def tauZH (a : Fin (2 ^ n)) : Word (PG (2 ^ n)) :=
  if (a : ℕ) = 0 ∨ (a : ℕ) = 1 then FreeMonoid.of (.zz (o1 n) a)
  else FreeMonoid.of (.zx a (o0 n) (o1 n))

/-- The coset action `τ` of Definition A.2. -/
def tauA : Cos → HadamardPi.Gen (2 ^ n) → Word (PG (2 ^ n)) × Cos
  | .e, .Z a => (FreeMonoid.of (.zz (o1 n) a), .z)
  | .e, .X a b _ =>
    (if (a : ℕ) = 1 ∨ (b : ℕ) = 1 then FreeMonoid.of (.zx (notOne n a b) a b)
      else FreeMonoid.of (.zx (o1 n) a b), .z)
  | .e, .H a b _ => (FreeMonoid.of (.hh a b (o0 n) (o1 n)), .h)
  | .z, .Z a => (FreeMonoid.of (.zz (o1 n) a), .e)
  | .z, .X a b _ => (FreeMonoid.of (.zx (o1 n) a b), .e)
  | .z, .H a b _ =>
    (if (a : ℕ) = 1 ∨ (b : ℕ) = 1 then
        FreeMonoid.of (.zx b a b) * FreeMonoid.of (.hh a b (o0 n) (o1 n))
      else FreeMonoid.of (.hh a b (o0 n) (o1 n)), .hz)
  | .h, .Z a => (tauZH n a, .hz)
  | .h, .X a b _ => (tauX n true a b, .hz)
  | .h, .H a b _ => (FreeMonoid.of (.hh (o0 n) (o1 n) a b), .e)
  | .hz, .Z a => (tauZH n a, .h)
  | .hz, .X a b _ => (tauX n false a b, .h)
  | .hz, .H a b _ =>
    (if (a : ℕ) = 1 ∨ (b : ℕ) = 1 then
        FreeMonoid.of (.hh (o0 n) (o1 n) a b) * FreeMonoid.of (.zx a a b)
      else FreeMonoid.of (.hh (o0 n) (o1 n) a b), .z)

/-! ## σ: letters of `𝒫_N` as words over `𝒢_N` -/

/-- `X_[c,d]` over `𝒢_N`, whatever the order of `c ≠ d` (Equation (e1)). -/
def Xw (c d : Fin (2 ^ n)) : Word (HadamardPi.Gen (2 ^ n)) :=
  if h : c < d then FreeMonoid.of (.X c d h)
  else if h' : d < c then FreeMonoid.of (.X d c h') else 1

/-- `H_[c,d]` over `𝒢_N`: `X_[d,c] H_[d,c] X_[d,c]` when `d < c` (Equation (e2)). -/
def Hw (c d : Fin (2 ^ n)) : Word (HadamardPi.Gen (2 ^ n)) :=
  if h : c < d then FreeMonoid.of (.H c d h)
  else if h' : d < c then FreeMonoid.of (.X d c h') * FreeMonoid.of (.H d c h') * FreeMonoid.of (.X d c h')
  else 1

/-- `σ`. -/
def sigmaG : PG (2 ^ n) → Word (HadamardPi.Gen (2 ^ n))
  | .zz a c => FreeMonoid.of (.Z a) * FreeMonoid.of (.Z c)
  | .zx a c d => FreeMonoid.of (.Z a) * Xw n c d
  | .xx a b c d => Xw n a b * Xw n c d
  | .hh a b c d => Hw n a b * Hw n c d

/-! ## σ preserves the semantics -/

section Sem

open QCert.HadamardPi (LGen lprod lprod_push lprod_eq_of_check)

variable {n}

theorem vec2_inj {c d : Fin (2 ^ n)} (h : c ≠ d) : Function.Injective ![c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (simp at hij; exact absurd hij (by simpa using h)) |
    (simp at hij; exact absurd hij.symm (by simpa using h))

theorem lmat_X (c d : Fin (2 ^ n)) :
    LGen.mat HadamardPi.invSqrt2 (LGen.X c d) = xM c d := rfl

theorem lmat_H (c d : Fin (2 ^ n)) :
    LGen.mat HadamardPi.invSqrt2 (LGen.H c d) = hM invSqrt2 c d := rfl

/-- `X_[d,c] = X_[c,d]`. -/
theorem xM_symm {c d : Fin (2 ^ n)} (h : c ≠ d) :
    (xM c d : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) = xM d c := by
  have e := lprod_eq_of_check (m := 2) [LGen.X 1 0] [LGen.X 0 1] (by decide +kernel)
  have := congrArg (levelMat ![d, c]) e
  rw [← lprod_push _ (vec2_inj (Ne.symm h)), ← lprod_push _ (vec2_inj (Ne.symm h))] at this
  simpa [lprod, LGen.push, lmat_X] using this

/-- `H_[c,d] = X_[d,c] H_[d,c] X_[d,c]`. -/
theorem hM_rev {c d : Fin (2 ^ n)} (h : c ≠ d) :
    (hM invSqrt2 c d : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ) = xM d c * hM invSqrt2 d c * xM d c := by
  have e := lprod_eq_of_check (m := 2) [LGen.H 1 0] [LGen.X 0 1, LGen.H 0 1, LGen.X 0 1]
    (by decide +kernel)
  have := congrArg (levelMat ![d, c]) e
  rw [← lprod_push _ (vec2_inj (Ne.symm h)), ← lprod_push _ (vec2_inj (Ne.symm h))] at this
  simpa [lprod, LGen.push, lmat_X, lmat_H, Matrix.mul_assoc] using this

theorem wordMat_Xw {c d : Fin (2 ^ n)} (h : c ≠ d) :
    HadamardPi.wordMat HadamardPi.invSqrt2 (Xw n c d) = xM c d := by
  unfold Xw
  split_ifs with h1 h2
  · simp [HadamardPi.wordMat, HadamardPi.genMat, xM, HadamardPi.Xmat]
  · simp only [HadamardPi.wordMat, FreeMonoid.lift_eval_of, HadamardPi.genMat]
    exact (xM_symm h).symm
  · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) h

theorem wordMat_Hw {c d : Fin (2 ^ n)} (h : c ≠ d) :
    HadamardPi.wordMat HadamardPi.invSqrt2 (Hw n c d) = hM invSqrt2 c d := by
  unfold Hw
  split_ifs with h1 h2
  · simp [HadamardPi.wordMat, HadamardPi.genMat, hM, HadamardPi.Hmat]
  · rw [hM_rev h]
    simp [HadamardPi.wordMat, HadamardPi.genMat, hM, xM, HadamardPi.Hmat, HadamardPi.Xmat,
      Matrix.mul_assoc]
  · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) h

theorem pMat_sigma {x : PG (2 ^ n)} (hx : x.Proper) :
    pMat invSqrt2 x = HadamardPi.wordMat HadamardPi.invSqrt2 (sigmaG n x) := by
  cases x with
  | zz a c => simp [sigmaG, pMat, HadamardPi.wordMat, HadamardPi.genMat, negM, HadamardPi.Zmat]
  | zx a c d =>
    simp only [sigmaG, pMat, map_mul, ← wordMat_Xw (n := n) hx]
    simp [HadamardPi.wordMat, HadamardPi.genMat, negM, HadamardPi.Zmat]
  | xx a b c d =>
    simp only [sigmaG, pMat, map_mul, wordMat_Xw hx.1, wordMat_Xw hx.2]
  | hh a b c d =>
    simp only [sigmaG, pMat, map_mul, wordMat_Hw hx.1, wordMat_Hw hx.2]

/-- σ preserves the semantics of proper words. -/
theorem sigma_sem {u : Word (PG (2 ^ n))} (hu : ProperW u) :
    pSem u = HadamardPi.wordMat HadamardPi.invSqrt2 (FreeMonoid.lift (sigmaG n) u) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp [pSem]
  | mul_of x u ih =>
    have e1 : pSem (FreeMonoid.of x * u) = pMat invSqrt2 x * pSem u := by
      simp [pSem, pWord]
    rw [e1, map_mul, map_mul, FreeMonoid.lift_eval_of, pMat_sigma (hu x (by simp)),
      ih fun y hy => hu y (by simp [hy])]

end Sem

/-! ## The reduction -/

/-- Hypothesis (a): for every proper letter `x`, `τ**(ε, σ(x)) = (v, ε)` with
`v ≈ x` (the equations (DE-ZZ), (DE-ZX), (DE-XX), (DE-HH)). -/
def ItemA : Prop :=
  ∀ x : PG (2 ^ n), x.Proper →
    (hstar (tauA n) Cos.e (sigmaG n x)).2 = Cos.e ∧
      Derivable (Fig8 n) (hstar (tauA n) Cos.e (sigmaG n x)).1 (FreeMonoid.of x)

/-- Hypothesis (b): for every relation of Figure 6 and every coset, `τ**` reaches
the same coset along both sides, with words equal by Figure 8. -/
def ItemB : Prop :=
  ∀ (c : Cos) (w w' : Word (HadamardPi.Gen (2 ^ n))), HadamardPi.Fig6 w w' →
    (hstar (tauA n) c w).2 = (hstar (tauA n) c w').2 ∧
      Derivable (Fig8 n) (hstar (tauA n) c w).1 (hstar (tauA n) c w').1

variable {n}

/-- Claim A for proper words. -/
theorem claimA_proper (hA : ItemA n) (v : Word (PG (2 ^ n))) (hv : ProperW v) :
    (hstar (tauA n) Cos.e (FreeMonoid.lift (sigmaG n) v)).2 = Cos.e ∧
      Derivable (Fig8 n) (hstar (tauA n) Cos.e (FreeMonoid.lift (sigmaG n) v)).1 v := by
  induction v using FreeMonoid.inductionOn' with
  | one => exact ⟨rfl, Derivable.refl _⟩
  | mul_of x v ih =>
    have hx := hA x (hv x (by simp))
    have ih' := ih fun y hy => hv y (by simp [hy])
    rw [map_mul, FreeMonoid.lift_eval_of, hstar_mul, hx.1]
    exact ⟨ih'.1, hx.2.mul ih'.2⟩

/-- **Theorem 4.10** from the two hypotheses of the Reidemeister–Schreier theorem. -/
theorem thm410_of (hA : ItemA n) (hB : ItemB n) : Thm410 n := by
  intro u v hu hv h
  have hs : FreeMonoid.lift (HadamardPi.sem (2 ^ n)) (FreeMonoid.lift (sigmaG n) u) =
      FreeMonoid.lift (HadamardPi.sem (2 ^ n)) (FreeMonoid.lift (sigmaG n) v) := by
    apply Subtype.ext; apply Subtype.ext
    rw [HadamardPi.lift_sem_val, HadamardPi.lift_sem_val, ← sigma_sem hu, ← sigma_sem hv, h]
  have hd := (HadamardPi.theorem_4_14 (2 ^ n)).complete hs
  have hb := rs_claimB (tauA n) hB hd Cos.e
  exact ((claimA_proper hA u hu).2.symm.trans hb.2).trans (claimA_proper hA v hv).2

end QCert.RealCliffordCH.Sec8
