/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Units of the presented three-qubit Clifford+CS monoid

Every generator has finite order, as already proved on an adjacent pair.
Thus words lift into the units of their syntactic quotient. Equality there
is exactly derivability; the concrete matrix semantics plays no role.
-/
import QCert.CliffordCS3.Rewrite

namespace QCert.CliffordCS3.Three.QuotientGroup

abbrev M := (conGen Rel).Quotient
abbrev G := Mˣ

def q : Word Gen →* M := (conGen Rel).mk'

theorem generator_eighth (x : Gen) : Derivable Rel ((FreeMonoid.of x) ^ 8) 1 := by
  cases x with
  | i => exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.I ^ 8) (v := 1) (by decide +kernel))
  | K₀ => exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Ku ^ 8) (v := 1) (by decide +kernel))
  | K₁ => exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Kl ^ 8) (v := 1) (by decide +kernel))
  | K₂ => exact Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Kl ^ 8) (v := 1) (by decide +kernel))
  | S₀ => exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Su ^ 8) (v := 1) (by decide +kernel))
  | S₁ => exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Sl ^ 8) (v := 1) (by decide +kernel))
  | S₂ => exact Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Sl ^ 8) (v := 1) (by decide +kernel))
  | CS₀₁ => exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.CS ^ 8) (v := 1) (by decide +kernel))
  | CS₁₂ => exact Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.CS ^ 8) (v := 1) (by decide +kernel))

def genUnit (x : Gen) : G where
  val := q (FreeMonoid.of x)
  inv := q (FreeMonoid.of x) ^ 7
  val_inv := by
    rw [← pow_succ']
    have h := (Con.eq (conGen Rel)).2 (generator_eighth x)
    simpa only [map_pow, map_one] using h
  inv_val := by
    rw [← pow_succ]
    have h := (Con.eq (conGen Rel)).2 (generator_eighth x)
    simpa only [map_pow, map_one] using h

def u : Word Gen →* G := FreeMonoid.lift genUnit

@[simp] theorem val_u (w : Word Gen) : (u w : M) = q w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x w ih =>
    rw [map_mul, Units.val_mul, ih, map_mul]
    change ((FreeMonoid.lift genUnit (FreeMonoid.of x) : M) * q w) =
      q (FreeMonoid.of x) * q w
    rw [FreeMonoid.lift_eval_of]
    rfl

theorem of_derivable {w v : Word Gen} (h : Derivable Rel w v) : u w = u v := by
  apply Units.ext
  simpa only [val_u] using (Con.eq (conGen Rel)).2 h

theorem to_derivable {w v : Word Gen} (h : u w = u v) : Derivable Rel w v := by
  apply (Con.eq (conGen Rel)).1
  have hv := congrArg (fun a : G => (a : M)) h
  simpa only [val_u] using hv

end QCert.CliffordCS3.Three.QuotientGroup

