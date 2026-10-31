/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Word inverses for the recovery certificates
-/
import QCert.CliffordCS3.Three.LocalKZ

namespace QCert.CliffordCS3.Three.RecoveryWords

open QuotientGroup

def invGen : Gen → List Gen
  | .K₀ => [.i, .K₀]
  | .K₁ => [.i, .K₁]
  | .K₂ => [.i, .K₂]
  | g => [g, g, g]

def invW (w : Word Gen) : Word Gen :=
  FreeMonoid.ofList (w.toList.reverse.flatMap invGen)

theorem invGen_ok (g : Gen) :
    u (FreeMonoid.ofList (invGen g)) = (u (FreeMonoid.of g))⁻¹ := by
  cases g
  · apply eq_inv_of_mul_eq_one_left
    exact of_derivable (Derivable.of Rel.c1)
  · exact LocalKZ.K_inv 0
  · exact LocalKZ.K_inv 1
  · exact LocalKZ.K_inv 2
  · apply eq_inv_of_mul_eq_one_left
    exact of_derivable (Derivable.of (Rel.c3 0))
  · apply eq_inv_of_mul_eq_one_left
    exact of_derivable (Derivable.of (Rel.c3 1))
  · apply eq_inv_of_mul_eq_one_left
    exact of_derivable (Derivable.of (Rel.c3 2))
  · apply eq_inv_of_mul_eq_one_left
    exact of_derivable (Derivable.of (Rel.c5 0))
  · apply eq_inv_of_mul_eq_one_left
    exact of_derivable (Derivable.of (Rel.c5 1))

theorem u_invW (w : Word Gen) : u (invW w) = (u w)⁻¹ := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [invW]
  | mul_of g w ih =>
    have he : invW (FreeMonoid.of g * w) = invW w * FreeMonoid.ofList (invGen g) := by
      simp [invW, List.reverse_append, List.flatMap_append, FreeMonoid.ofList_append]
    rw [he, map_mul, ih, invGen_ok, map_mul, mul_inv_rev]

def commW (w v : Word Gen) : Word Gen := w * v * invW w * invW v

theorem u_commW (w v : Word Gen) :
    u (commW w v) = u w * u v * (u w)⁻¹ * (u v)⁻¹ := by
  simp only [commW, map_mul, u_invW]

end QCert.CliffordCS3.Three.RecoveryWords
