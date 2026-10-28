/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Theorem 21 from a source on flat letters

Several source presentations are not stated on wires: Bian and Selinger's
two-qubit Clifford+T and three-qubit Clifford+CS presentations have one
letter per gate and qubit, and the two-level presentations of Greylyn and
of Bian and Selinger have the one- and two-level matrices of a fixed
dimension as letters.  Their words denote matrices indexed by `Fin (2ⁿ)`.

For such a source, with its letters read as matrices over `ℚ(ω)`, the
encoding of the qubit gates preserves the semantics as soon as it does on
each generator (`flat_sem`), which is decided over `ℚ(ω)`; and Theorem 21
then takes the form `complete_of_flat`.  Decoding the encoding of every
circuit derives the circuit as soon as it does for every generator
(`derivable_lift_comp`, Lemma 19 for a flat encoding).
-/
import QCert.Minimality.Cross
import QCert.Exact.Roots

namespace QCert.Minimality

open Matrix QCert.Circuit

/-! ### Reading a `dᵏ × dᵏ` matrix on wires -/

section OfMat

variable {R : Type*} {d k : ℕ}

theorem ofMat_mul [CommRing R] (A B : Matrix (Fin (d ^ k)) (Fin (d ^ k)) R) :
    ofMat (A * B) = ofMat A * ofMat B := by
  simp only [ofMat]
  exact (Matrix.submatrix_mul_equiv A B _ _ _).symm

theorem ofMat_one [CommRing R] : ofMat (1 : Matrix (Fin (d ^ k)) (Fin (d ^ k)) R) = 1 :=
  Matrix.submatrix_one_equiv _

theorem ofMat_injective :
    Function.Injective (ofMat : Matrix (Fin (d ^ k)) (Fin (d ^ k)) R → Op R d k) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h (finFunctionFinEquiv.symm i)) (finFunctionFinEquiv.symm j)
  simpa [ofMat] using this

theorem ofMat_map' {S : Type*} (f : R → S) (M : Matrix (Fin (d ^ k)) (Fin (d ^ k)) R) :
    ofMat (M.map f) = (ofMat M).map f := rfl

end OfMat

/-- `ℤ[ω] → ℂ` factors through `ℚ(ω)`. -/
theorem ZOmega.toC_comp_toQ : QOmega.toC.comp ZOmega.toQ = ZOmega.toC := by
  refine ZQuartic.hom_ext (R := ℂ) ?_
  rw [RingHom.comp_apply, ZOmega.toC_X, show ZOmega.toQ ZQuartic.X = Quartic.X from
    ZQuartic.lift_X _ _]
  exact QOmega.toC_X

theorem ZOmega.toC_toQ (x : ZOmega) : QOmega.toC (ZOmega.toQ x) = ZOmega.toC x :=
  congrArg (fun f : ZOmega →+* ℂ => f x) ZOmega.toC_comp_toQ

/-! ### The semantics of an encoding into flat letters -/

section Flat

variable {G : ℕ → Type} {Y : Type*}

/-- An encoding into flat letters whose matrices over `ℚ(ω)` agree with the
gates' on every generator preserves the semantics. -/
theorem flat_sem (S : ScaledOps G ZOmega 2) (semT : GateSem G ℂ 2)
    (hT : semT.toOps = S.toOps ZOmega.toC Qubit.invSqrt2) {n : ℕ}
    (matQ : Y → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QOmega) (e : Gen G n → FreeMonoid Y)
    (he : ∀ g, ofMat (FreeMonoid.lift matQ (e g)) =
      QOmega.invSqrt2 ^ S.exGen g • (S.ops.gen g).map ZOmega.toQ)
    (w : Circuit G n) :
    ofMat ((FreeMonoid.lift matQ (FreeMonoid.lift e w)).map QOmega.toC) =
      (semT.sem n w : Op ℂ 2 n) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [map_one, map_one, map_one, Submonoid.coe_one,
      Matrix.map_one _ (map_zero _) (map_one _), ofMat_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, Matrix.map_mul, ofMat_mul, ih, map_mul, Submonoid.coe_mul,
      FreeMonoid.lift_eval_of]
    congr 1
    rw [ofMat_map', he g, GateSem.sem_val,
      show semT.toOps.eval n (FreeMonoid.of g) = semT.toOps.gen g from FreeMonoid.lift_eval_of _ _,
      hT, ScaledOps.gen_toOps]
    ext s t
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow,
      QOmega.toC_invSqrt2, ZOmega.toC_toQ]

/-- Theorem 21 for a source on flat letters whose matrices are read over
`ℚ(ω)` through an injective map. -/
theorem complete_of_flat {M' : Type*} [Monoid M'] (S : ScaledOps G ZOmega 2)
    (semT : GateSem G ℂ 2) (hT : semT.toOps = S.toOps ZOmega.toC Qubit.invSqrt2) {n : ℕ}
    (Γ : WRel (Gen G n)) (Γs : WRel Y) (semY : FreeMonoid Y →* M')
    (κ : M' →* Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hκ : Function.Injective κ)
    (matQ : Y → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QOmega)
    (hY : ∀ y, κ (semY (FreeMonoid.of y)) = (matQ y).map QOmega.toC)
    (e : Gen G n → FreeMonoid Y)
    (he : ∀ g, ofMat (FreeMonoid.lift matQ (e g)) =
      QOmega.invSqrt2 ^ S.exGen g • (S.ops.gen g).map ZOmega.toQ)
    (D : FreeMonoid Y → Circuit G n)
    (hsrc : ∀ a b, semY a = semY b → Derivable Γs a b)
    (hD : ∀ a b, Derivable Γs a b → Derivable Γ (D a) (D b))
    (hDE : ∀ w, Derivable Γ (D (FreeMonoid.lift e w)) w) :
    ∀ w v : Circuit G n, semT.sem n w = semT.sem n v → Derivable Γ w v := by
  have hκY : κ.comp semY = (QOmega.toC.mapMatrix : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QOmega →+*
      Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ).toMonoidHom.comp (FreeMonoid.lift matQ) := by
    refine FreeMonoid.hom_eq fun y => ?_
    simp only [MonoidHom.comp_apply, hY, FreeMonoid.lift_eval_of]
    rfl
  refine complete_of_transfer_map Γ Γs (semT.sem n) semY (FreeMonoid.lift e) D
    (fun U => ofMat (κ U)) (ofMat_injective.comp hκ) (fun U => (U : Op ℂ 2 n)) (fun w => ?_)
    hsrc hD hDE
  have := congrArg (fun f => f (FreeMonoid.lift e w)) hκY
  simp only [MonoidHom.comp_apply] at this
  show ofMat (κ (semY (FreeMonoid.lift e w))) = (semT.sem n w : Op ℂ 2 n)
  rw [this]
  exact flat_sem S semT hT matQ e he w

/-- Lemma 19 for a flat encoding: decoding the encoding of every circuit
derives the circuit as soon as it does for every generator. -/
theorem derivable_lift_comp {n : ℕ} {Γ : WRel (Gen G n)} (e : Gen G n → FreeMonoid Y)
    (D : FreeMonoid Y →* Circuit G n) (h : ∀ g, Derivable Γ (D (e g)) (FreeMonoid.of g))
    (w : Circuit G n) : Derivable Γ (D (FreeMonoid.lift e w)) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, FreeMonoid.lift_eval_of]
    exact (h g).mul ih

end Flat

end QCert.Minimality
