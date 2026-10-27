/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of CNOTdihe₂ (Theorem 22 (6))

Appendix H: no encoding is needed, Amy, Chen and Ross's presentation having
the same generators (`QCert.CNOTDihedral`: the gates `ω, X, T, CNOT` and the
swap, the relations R₁–R₁₃ of their Figure 1 with the laws of the
symmetry).  A circuit read as theirs (`enc`) has the same matrix
(`sem_enc`), their relations are derivable from Figure 7
(`rel_derivable`), and reading back is the identity (`tr_enc`); so their
completeness gives ours (Theorem 21, `complete_of_source`).
-/
import QCert.Minimality.CNOTDihedral.Derivations
import QCert.Minimality.CNOTDihedral.Semantics
import QCert.CNOTDihedral.Theorem

namespace QCert.Minimality.CNOTDihedral

open Matrix Qubit

/-- Our circuits read as Amy–Chen–Ross's. -/
abbrev enc (n : ℕ) : Circuit Gate n →* Circuit QCert.CNOTDihedral.Gate n := Circuit.rename unGate n

theorem tr_enc {n : ℕ} (w : Circuit Gate n) : tr n (enc n w) = w := by
  have hg : ∀ {m : ℕ} (g : Gen Gate m), Gen.map trGate (Gen.map unGate g) = g := by
    intro m g
    induction g with
    | gate0 c => cases c; rfl
    | gate1 c => cases c <;> rfl
    | gate2 c => cases c <;> rfl
    | gate3 c => exact nomatch c
    | up g ih => exact congrArg Gen.up ih
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, ih]
    show FreeMonoid.of (Gen.map trGate (Gen.map unGate g)) * w = _
    rw [hg]

/-! ### The same matrices -/

theorem idx1 (s : State 2 1) : (finFunctionFinEquiv s : ℕ) = s 0 := by
  rw [finFunctionFinEquiv_apply]; simp

theorem idx2 (s : State 2 2) : (finFunctionFinEquiv s : ℕ) = s 0 + 2 * s 1 := by
  rw [finFunctionFinEquiv_apply]; simp [Fin.sum_univ_two]; ring

/-- The index `a + 2 b` of the digits `a` (wire `0`) and `b` (wire `1`). -/
def pair (a b : Fin 2) : Fin (2 ^ 2) := ⟨a + 2 * b, by omega⟩

theorem ofMat1 (M : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) (s t : State 2 1) :
    ofMat M s t = M (Fin.cast (by norm_num) (s 0)) (Fin.cast (by norm_num) (t 0)) := by
  show M (finFunctionFinEquiv s) (finFunctionFinEquiv t) = _
  congr 1 <;> exact Fin.ext (idx1 _)

theorem ofMat2 (M : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ) (s t : State 2 2) :
    ofMat M s t = M (pair (s 0) (s 1)) (pair (t 0) (t 1)) := by
  show M (finFunctionFinEquiv s) (finFunctionFinEquiv t) = _
  congr 1 <;> exact Fin.ext (idx2 _)

theorem matX_eq : ofMat QCert.CNOTDihedral.matX = xC := by
  ext s t
  rw [ofMat1]
  simp only [xC]
  generalize s 0 = a
  generalize t 0 = b
  fin_cases a <;> fin_cases b <;> simp [QCert.CNOTDihedral.matX]

theorem matT_eq : ofMat QCert.CNOTDihedral.matT = tC := by
  ext s t
  rw [ofMat1]
  simp only [tC]
  generalize s 0 = a
  generalize t 0 = b
  fin_cases a <;> fin_cases b <;> simp [QCert.CNOTDihedral.matT]

theorem matCX_eq : ofMat QCert.CNOTDihedral.matCX = cnotC := by
  ext s t
  rw [ofMat2]
  simp only [cnotC]
  generalize s 0 = a
  generalize s 1 = b
  generalize t 0 = c
  generalize t 1 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [QCert.CNOTDihedral.matCX, pair]

theorem matSW_eq : ofMat QCert.CNOTDihedral.matSW = swapC := by
  ext s t
  rw [ofMat2]
  simp only [swapC]
  generalize s 0 = a
  generalize s 1 = b
  generalize t 0 = c
  generalize t 1 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [QCert.CNOTDihedral.matSW, pair]

theorem gen_enc : ∀ {n : ℕ} (g : Gen Gate n),
    QCert.CNOTDihedral.S.gen (Gen.map unGate g) = sem.gen g
  | _, .gate0 c => by cases c; rfl
  | _, .gate1 c => by
    cases c
    · show onBottomU _ = onBottomU _; congr 1; exact Subtype.ext matX_eq
    · show onBottomU _ = onBottomU _; congr 1; exact Subtype.ext matT_eq
  | _, .gate2 c => by
    cases c
    · show onBottomU _ = onBottomU _; congr 1; exact Subtype.ext matCX_eq
    · show onBottomU _ = onBottomU _; congr 1; exact Subtype.ext matSW_eq
  | _, .gate3 c => nomatch c
  | _, .up g => by
    show onTopU 1 _ = onTopU 1 _
    rw [gen_enc g]

/-- A circuit read as Amy–Chen–Ross's has the same matrix. -/
theorem sem_enc {n : ℕ} (w : Circuit Gate n) :
    QCert.CNOTDihedral.S.sem n (enc n w) = sem.sem n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih]
    congr 1
    simp only [Circuit.rename, FreeMonoid.map_of, GateSem.sem, FreeMonoid.lift_eval_of]
    exact gen_enc g

/-! ### Theorem 21 -/

/-- Theorem 22 (6) from the completeness of Amy, Chen and Ross's
presentation: CNOTdihe₂ is complete. -/
theorem complete_of_source
    (hsrc : ∀ n (w v : Circuit QCert.CNOTDihedral.Gate n),
      QCert.CNOTDihedral.S.sem n w = QCert.CNOTDihedral.S.sem n v →
        Derivable (QCert.CNOTDihedral.Theory n) w v) :
    pres.Complete fun n => sem.sem n := by
  intro n w v h
  refine complete_of_transfer (Lift (Padded (pres.Base fun _ => True)) n)
    (QCert.CNOTDihedral.Theory n) (sem.sem n) (QCert.CNOTDihedral.S.sem n) (enc n) (tr n)
    sem_enc (hsrc n) (fun a b hab => ?_) (fun w => by rw [tr_enc]) w v h
  exact derivable_rename trGate (fun k w v r => rel_derivable r) hab

/-- Theorem 22 (6): CNOTdihe₂ is complete, given the completeness of Amy,
Chen and Ross's presentation as formalised in `QCert.CNOTDihedral`. -/
theorem complete : pres.Complete fun n => sem.sem n :=
  complete_of_source fun n _ _ h => (QCert.CNOTDihedral.presentation n).complete h

end QCert.Minimality.CNOTDihedral
