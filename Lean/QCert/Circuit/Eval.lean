/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Evaluating circuits over any commutative ring

`GateOps` gives a gate set operators over an arbitrary commutative ring,
with no unitarity, and `GateOps.eval` evaluates circuits the same way as
`GateSem.sem`.  Evaluation commutes with ring homomorphisms
(`GateOps.eval_map`), so an equation between circuits can be decided over a
computable ring `E` (by `decide +kernel`) and carried along a homomorphism
`E →+* ℂ` to the unitary semantics (`GateSem.sem_eq_of_eval`).
-/
import QCert.Circuit.Semantics

namespace QCert

open Matrix

/-- Operators of a gate set over a commutative ring. -/
structure GateOps (Gate : ℕ → Type) (R : Type*) [CommRing R] (d : ℕ) where
  scalar : Gate 0 → R
  gate1 : Gate 1 → Op R d 1
  gate2 : Gate 2 → Op R d 2
  gate3 : Gate 3 → Op R d 3

namespace GateOps

variable {Gate : ℕ → Type} {R R' : Type*} [CommRing R] [CommRing R'] {d : ℕ}
  (O : GateOps Gate R d)

/-- The operator of a generator. -/
def gen : {n : ℕ} → Gen Gate n → Op R d n
  | _, .gate0 g => O.scalar g • 1
  | _, .gate1 g => onBottom (O.gate1 g)
  | _, .gate2 g => onBottom (O.gate2 g)
  | _, .gate3 g => onBottom (O.gate3 g)
  | _, .up g => onTop 1 (gen g)

/-- The operator of a circuit, composed in operator order. -/
def eval (n : ℕ) : Circuit Gate n →* Op R d n := FreeMonoid.lift O.gen

/-- The operators read through a ring homomorphism. -/
def map (f : R →+* R') : GateOps Gate R' d where
  scalar g := f (O.scalar g)
  gate1 g := (O.gate1 g).map f
  gate2 g := (O.gate2 g).map f
  gate3 g := (O.gate3 g).map f

theorem onBottom_map (f : R →+* R') {n k : ℕ} (G : Op R d k) :
    onBottom (n := n) (G.map f) = (onBottom G).map f := by
  ext s t; simp only [onBottom_apply, map_apply]; split_ifs <;> simp

theorem onTop_map (f : R →+* R') {n k : ℕ} (M : Op R d n) :
    onTop k (M.map f) = (onTop k M).map f := by
  ext s t; simp only [onTop_apply, map_apply]; split_ifs <;> simp

theorem gen_map (f : R →+* R') {n : ℕ} (g : Gen Gate n) :
    (O.map f).gen g = (O.gen g).map f := by
  induction g with
  | gate0 c =>
    ext s t; by_cases h : s = t <;> simp [gen, map, one_apply, h]
  | gate1 c => exact onBottom_map f _
  | gate2 c => exact onBottom_map f _
  | gate3 c => exact onBottom_map f _
  | up g ih => show onTop 1 _ = _; rw [ih]; exact onTop_map f _

theorem eval_map (f : R →+* R') {n : ℕ} (w : Circuit Gate n) :
    (O.map f).eval n w = (O.eval n w).map f := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [Matrix.map_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul, ih, Matrix.map_mul]
    congr 1
    exact O.gen_map f g

end GateOps

namespace GateSem

variable {Gate : ℕ → Type} {R E : Type*} [CommRing R] [StarRing R] [CommRing E] {d : ℕ}
  (S : GateSem Gate R d)

/-- The operators of a gate set, forgetting unitarity. -/
def toOps : GateOps Gate R d where
  scalar g := S.scalar g
  gate1 g := S.gate1 g
  gate2 g := S.gate2 g
  gate3 g := S.gate3 g

theorem gen_val {n : ℕ} (g : Gen Gate n) : (S.gen g).1 = S.toOps.gen g := by
  induction g with
  | gate0 c => rfl
  | gate1 c => rfl
  | gate2 c => rfl
  | gate3 c => rfl
  | up g ih => show onTop 1 _ = onTop 1 _; rw [ih]

theorem sem_val {n : ℕ} (w : Circuit Gate n) : (S.sem n w).1 = S.toOps.eval n w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, map_mul, Submonoid.coe_mul, ih]
    congr 1
    exact S.gen_val g

/-- An equation decided over a ring `E` whose operators the gate set's
are the image of holds in the unitary semantics. -/
theorem sem_eq_of_eval (f : E →+* R) (O : GateOps Gate E d) (hO : S.toOps = O.map f)
    {n : ℕ} {w v : Circuit Gate n} (h : O.eval n w = O.eval n v) : S.sem n w = S.sem n v := by
  apply Subtype.ext
  rw [sem_val, sem_val, hO, GateOps.eval_map, GateOps.eval_map, h]

end GateSem

end QCert
