/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Comparing circuits of two gate sets

An encoding (Definition 18) preserves the semantics when each gate and the
circuit replacing it have the same matrix.  When both gate sets are given
by scaled integer matrices (`ScaledOps`), that is decided on row tries
(`sem_eq_cross`); and a substitution that preserves the matrix of every
gate preserves the matrix of every circuit (`GateSubst.sem_map`).
-/
import QCert.Minimality.Subst
import QCert.Minimality.Qubit
import QCert.Minimality.Qutrit

namespace QCert.Minimality

open QCert.Circuit

section Cross

variable {G G' : ℕ → Type} {K : Type} [CommRing K] {R : Type} [CommRing R] {d : ℕ}

/-- Two circuits of two scaled gate sets have the same matrix when their
integer matrices, scaled to balance the factors `σ`, agree. -/
theorem ScaledOps.eval_toOps_cross (A : ScaledOps G K d) (B : ScaledOps G' K d)
    (f : K →+* R) (σ s : R) (s' : K) (hs' : f s' = s) (hs : s * σ = 1)
    {n : ℕ} {w : Circuit G n} {v : Circuit G' n} (j k : ℕ) (hE : A.ex w + j = B.ex v + k)
    (h : s' ^ j • A.ops.eval n w = s' ^ k • B.ops.eval n v) :
    (A.toOps f σ).eval n w = (B.toOps f σ).eval n v := by
  have h' : s ^ j • (A.ops.eval n w).map f = s ^ k • (B.ops.eval n v).map f := by
    have := congrArg (fun M => M.map f) h
    simp only [Matrix.map_smul' _ _ _ (map_mul f), map_pow, hs'] at this
    exact this
  rw [A.eval_toOps, B.eval_toOps]
  have e1 : (σ * s) ^ j = 1 := by rw [mul_comm, hs, one_pow]
  have e2 : (σ * s) ^ k = 1 := by rw [mul_comm, hs, one_pow]
  calc σ ^ A.ex w • (A.ops.eval n w).map f
      = σ ^ A.ex w • ((σ * s) ^ j • (A.ops.eval n w).map f) := by rw [e1, one_smul]
    _ = σ ^ (A.ex w + j) • (s ^ j • (A.ops.eval n w).map f) := by
        simp only [mul_pow, pow_add, smul_smul, mul_assoc]
    _ = σ ^ (B.ex v + k) • (s ^ k • (B.ops.eval n v).map f) := by rw [hE, h']
    _ = σ ^ B.ex v • ((σ * s) ^ k • (B.ops.eval n v).map f) := by
        simp only [mul_pow, pow_add, smul_smul, mul_assoc]
    _ = _ := by rw [e2, one_smul]

/-- Two circuits of two qubit gate sets given by scaled ℤ[ω] matrices have
the same matrix when the scaled integer row tries agree. -/
theorem sem_eq_cross (semA : GateSem G ℂ 2) (A : ScaledOps G ZOmega 2)
    (hA : semA.toOps = A.toOps ZOmega.toC Qubit.invSqrt2)
    (semB : GateSem G' ℂ 2) (B : ScaledOps G' ZOmega 2)
    (hB : semB.toOps = B.toOps ZOmega.toC Qubit.invSqrt2) {n : ℕ} {w : Circuit G n}
    {v : Circuit G' n}
    (h : (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (B.ex v - A.ex w)) (evalRows A.ops n w) =
      (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (A.ex w - B.ex v)) (evalRows B.ops n v)) :
    (semA.sem n w : Op ℂ 2 n) = semB.sem n v := by
  rw [GateSem.sem_val, GateSem.sem_val, hA, hB]
  refine A.eval_toOps_cross B ZOmega.toC Qubit.invSqrt2 _ ZOmega.sqrt2 ZOmega.toC_sqrt2
    (mul_inv_cancel₀ QCert.sqrt2_ne_zero) (B.ex v - A.ex w) (A.ex w - B.ex v) (by omega) ?_
  rw [← den_evalRows A.ops, ← den_evalRows B.ops, ← LinRep.den_smul, ← LinRep.den_smul, h]

/-- `sem_eq_cross` for qutrit gate sets over ℤ[ζ₁₂], `H` scaled by `√3`. -/
theorem sem_eq_cross3 (semA : GateSem G ℂ 3) (A : ScaledOps G ZZeta 3)
    (hA : semA.toOps = A.toOps ZZeta.toC Qutrit.invSqrt3)
    (semB : GateSem G' ℂ 3) (B : ScaledOps G' ZZeta 3)
    (hB : semB.toOps = B.toOps ZZeta.toC Qutrit.invSqrt3) {n : ℕ} {w : Circuit G n}
    {v : Circuit G' n}
    (h : (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (B.ex v - A.ex w)) (evalRows A.ops n w) =
      (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (A.ex w - B.ex v)) (evalRows B.ops n v)) :
    (semA.sem n w : Op ℂ 3 n) = semB.sem n v := by
  rw [GateSem.sem_val, GateSem.sem_val, hA, hB]
  refine A.eval_toOps_cross B ZZeta.toC Qutrit.invSqrt3 _ ZZeta.sqrt3 ZZeta.toC_sqrt3
    (mul_inv_cancel₀ ZZeta.sqrt3_ne_zero) (B.ex v - A.ex w) (A.ex w - B.ex v) (by omega) ?_
  rw [← den_evalRows A.ops, ← den_evalRows B.ops, ← LinRep.den_smul, ← LinRep.den_smul, h]

end Cross

/-! ### Substitutions that preserve the semantics -/

section SemMap

variable {G G' : ℕ → Type} {R : Type*} [CommRing R] [StarRing R] {d : ℕ}

/-- A substitution that gives each gate a circuit with the gate's matrix
preserves the matrix of every circuit. -/
theorem GateSubst.sem_map (Φ : GateSubst G G') (S : GateSem G R d) (S' : GateSem G' R d)
    (h0 : ∀ c, S'.sem 0 (Φ.φ0 c) = S.sem 0 (g0 c))
    (h1 : ∀ c, S'.sem 1 (Φ.φ1 c) = S.sem 1 (g1 c))
    (h2 : ∀ c, S'.sem 2 (Φ.φ2 c) = S.sem 2 (g2 c))
    (h3 : ∀ c, S'.sem 3 (Φ.φ3 c) = S.sem 3 (g3 c)) :
    ∀ {n : ℕ} (w : Circuit G n), S'.sem n (Φ.map n w) = S.sem n w := by
  have hgen : ∀ {n : ℕ} (g : Gen G n), S'.sem n (Φ.gen g) = S.gen g := by
    intro n g
    induction g with
    | @gate0 m c =>
      show S'.sem (m + 0) (Circuit.pad m (Φ.φ0 c)) = S.gen ((Gen.gate0 c : Gen G 0).pad m)
      rw [S'.sem_pad, h0]
      apply Subtype.ext
      rw [S.gen_pad]
      show onBottom (S.sem 0 (g0 c) : Op R d 0) = _
      rw [show S.sem 0 (g0 c) = S.gen (Gen.gate0 c) from FreeMonoid.lift_eval_of _ _]
    | @gate1 m c =>
      show S'.sem (m + 1) (Circuit.pad m (Φ.φ1 c)) = S.gen ((Gen.gate1 c : Gen G (0 + 1)).pad m)
      rw [S'.sem_pad, h1]
      apply Subtype.ext
      rw [S.gen_pad]
      show onBottom (S.sem 1 (g1 c) : Op R d 1) = _
      rw [show S.sem 1 (g1 c) = S.gen (Gen.gate1 c) from FreeMonoid.lift_eval_of _ _]
    | @gate2 m c =>
      show S'.sem (m + 2) (Circuit.pad m (Φ.φ2 c)) = S.gen ((Gen.gate2 c : Gen G (0 + 2)).pad m)
      rw [S'.sem_pad, h2]
      apply Subtype.ext
      rw [S.gen_pad]
      show onBottom (S.sem 2 (g2 c) : Op R d 2) = _
      rw [show S.sem 2 (g2 c) = S.gen (Gen.gate2 c) from FreeMonoid.lift_eval_of _ _]
    | @gate3 m c =>
      show S'.sem (m + 3) (Circuit.pad m (Φ.φ3 c)) = S.gen ((Gen.gate3 c : Gen G (0 + 3)).pad m)
      rw [S'.sem_pad, h3]
      apply Subtype.ext
      rw [S.gen_pad]
      show onBottom (S.sem 3 (g3 c) : Op R d 3) = _
      rw [show S.sem 3 (g3 c) = S.gen (Gen.gate3 c) from FreeMonoid.lift_eval_of _ _]
    | @up m g ih =>
      show S'.sem (m + 1) (shift (Φ.gen g)) = onTopU 1 (S.gen g)
      rw [S'.sem_shift, ih]
  intro n w
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul (Φ.map n), map_mul (S'.sem n), map_mul (S.sem n), ih, Φ.map_of, hgen]
    rw [show S.sem n (FreeMonoid.of g) = S.gen g from FreeMonoid.lift_eval_of _ _]

end SemMap

/-! ### The controlled-`Z` gate -/

open Qubit in
/-- `⟦CZ⟧ |x, y⟩ = (-1)^{xy} |x, y⟩` over ℤ[ω]. -/
def czZ : Op ZOmega 2 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then (-1) ^ ((s 0 : ℕ) * (s 1 : ℕ)) else 0

open Qubit in
/-- `⟦CZ⟧ |x, y⟩ = (-1)^{xy} |x, y⟩`. -/
noncomputable def czC : Op ℂ 2 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then (-1) ^ ((s 0 : ℕ) * (s 1 : ℕ)) else 0

open Qubit in
theorem czC_eq : czC = invSqrt2 ^ 0 • czZ.map ZOmega.toC := by
  ext s t; simp only [czC, czZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

open Qubit in
theorem czC_mem : czC ∈ Matrix.unitaryGroup (State 2 2) ℂ := by
  rw [czC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

/-! ### Real semantics read over `ℂ` -/

/-- A semantics whose matrices are the images of another's under a ring
map gives the images of its circuits. -/
theorem GateSem.sem_map_of {G : ℕ → Type} {R R' : Type} [CommRing R] [StarRing R] [CommRing R']
    [StarRing R'] {d : ℕ} (S : GateSem G R d) (S' : GateSem G R' d) (f : R →+* R')
    (h : S'.toOps = S.toOps.map f) {n : ℕ} (w : Circuit G n) :
    (S'.sem n w : Op R' d n) = (S.sem n w : Op R d n).map f := by
  rw [GateSem.sem_val, GateSem.sem_val, h, GateOps.eval_map]

/-- Theorem 21 for a source whose semantics lands in another monoid: the
target semantics is read off the source's through an injective map. -/
theorem complete_of_transfer_map {X Y : Type*} {M M' N : Type*} [Monoid M] [Monoid M']
    (Γ : WRel X) (Γs : WRel Y) (sem : FreeMonoid X →* M) (semS : FreeMonoid Y →* M')
    (E : FreeMonoid X → FreeMonoid Y) (D : FreeMonoid Y → FreeMonoid X)
    (φ : M' → N) (hφ : Function.Injective φ) (ψ : M → N)
    (hE : ∀ w, φ (semS (E w)) = ψ (sem w))
    (hsrc : ∀ a b, semS a = semS b → Derivable Γs a b)
    (hD : ∀ a b, Derivable Γs a b → Derivable Γ (D a) (D b))
    (hDE : ∀ w, Derivable Γ (D (E w)) w) :
    ∀ w v, sem w = sem v → Derivable Γ w v := by
  intro w v h
  have h1 : Derivable Γs (E w) (E v) := hsrc _ _ (hφ (by rw [hE, hE, h]))
  exact ((hDE w).symm.trans (hD _ _ h1)).trans (hDE v)

/-! ### Matrices indexed by `Fin (2 ^ k)` read on wires -/

theorem idx1 (s : State 2 1) : (finFunctionFinEquiv s : ℕ) = s 0 := by
  rw [finFunctionFinEquiv_apply]; simp

theorem idx2 (s : State 2 2) : (finFunctionFinEquiv s : ℕ) = s 0 + 2 * s 1 := by
  rw [finFunctionFinEquiv_apply]; simp [Fin.sum_univ_two]; ring

/-- The index `a + 2 b` of the digits `a` (wire `0`) and `b` (wire `1`). -/
def pair (a b : Fin 2) : Fin (2 ^ 2) := ⟨a + 2 * b, by omega⟩

theorem ofMat1 {R : Type*} (M : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) R) (s t : State 2 1) :
    ofMat M s t = M (Fin.cast (by norm_num) (s 0)) (Fin.cast (by norm_num) (t 0)) := by
  show M (finFunctionFinEquiv s) (finFunctionFinEquiv t) = _
  congr 1 <;> exact Fin.ext (idx1 _)

theorem idx3_1 (s : State 3 1) : (finFunctionFinEquiv s : ℕ) = s 0 := by
  rw [finFunctionFinEquiv_apply]; simp

theorem idx3_2 (s : State 3 2) : (finFunctionFinEquiv s : ℕ) = s 0 + 3 * s 1 := by
  rw [finFunctionFinEquiv_apply]; simp [Fin.sum_univ_two]; ring

/-- The index `a + 3 b` of the digits `a` (wire `0`) and `b` (wire `1`). -/
def pair3 (a b : Fin 3) : Fin (3 ^ 2) := ⟨a + 3 * b, by omega⟩

theorem ofMat3_1 {R : Type*} (M : Matrix (Fin (3 ^ 1)) (Fin (3 ^ 1)) R) (s t : State 3 1) :
    ofMat M s t = M (Fin.cast (by norm_num) (s 0)) (Fin.cast (by norm_num) (t 0)) := by
  show M (finFunctionFinEquiv s) (finFunctionFinEquiv t) = _
  congr 1 <;> exact Fin.ext (idx3_1 _)

theorem ofMat3_2 {R : Type*} (M : Matrix (Fin (3 ^ 2)) (Fin (3 ^ 2)) R) (s t : State 3 2) :
    ofMat M s t = M (pair3 (s 0) (s 1)) (pair3 (t 0) (t 1)) := by
  show M (finFunctionFinEquiv s) (finFunctionFinEquiv t) = _
  congr 1 <;> exact Fin.ext (idx3_2 _)

theorem ofMat2 {R : Type*} (M : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) R) (s t : State 2 2) :
    ofMat M s t = M (pair (s 0) (s 1)) (pair (t 0) (t 1)) := by
  show M (finFunctionFinEquiv s) (finFunctionFinEquiv t) = _
  congr 1 <;> exact Fin.ext (idx2 _)


end QCert.Minimality
