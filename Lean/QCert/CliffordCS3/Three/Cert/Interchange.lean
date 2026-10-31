/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The four-point Hadamard interchange equation in both cosets
-/
import QCert.CliffordCS3.Three.BlockInterchange
import QCert.CliffordCS3.Three.BasicCases

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.Cert.Interchange

open QuotientGroup LocalKZ RestrictedGauge BlockInterchange
open RestrictedGauge.Letter
noncomputable section

def verticalWord : List Letter := [t6,t5,k,t5,t6,t4,t5,k,t5,t4]
def horizontalWord : List Letter := [t4,t5,t6,t4,t5,k,t5,t4,t6,t5,t4,k]
def lhs : List Letter := verticalWord ++ horizontalWord
def rhs : List Letter := horizontalWord ++ verticalWord

theorem token_inv (d : Fin 7) : (u (token d))⁻¹ = u (token d) := by
  apply Monomial.inv_of_square
  simpa only [map_mul, map_one] using of_derivable (token_involution d)

theorem eval_vertical : Gauge.eval lift verticalWord = V := by
  simp only [Gauge.eval, verticalWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, lift, mul_one]
  simp only [V, V1, V2, PermutationBase.conj_def, PermutationRoutes.tokens,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_mul, map_one,
    mul_inv_rev, inv_one, token_inv, mul_one, mul_assoc]
  rfl

theorem eval_horizontal : Gauge.eval lift horizontalWord = BlockInterchange.H := by
  simp only [Gauge.eval, horizontalWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, lift, mul_one]
  simp only [BlockInterchange.H, BlockHorizontal.H, BlockHorizontal.F, PermutationFrames.frame,
    PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    map_mul, map_one, mul_inv_rev, inv_one, token_inv, mul_one, mul_assoc]
  rfl

theorem eval_append (a b : List Letter) : Gauge.eval lift (a ++ b) = Gauge.eval lift a * Gauge.eval lift b := by
  simp only [Gauge.eval, List.map_append, List.prod_append]

theorem lifted : Gauge.eval lift lhs = Gauge.eval lift rhs := by
  rw [lhs, rhs, eval_append, eval_append, eval_vertical, eval_horizontal]
  exact BlockInterchange.blocks_commute.eq

theorem equation (c : Bool) : Derivable Rel (hstar h c (word lhs)).1 (hstar h c (word rhs)).1 :=
  residuals_equal facts c lhs rhs 2 (by decide) (by decide) lifted

def rule (c : Bool) : Rule Rel := Rule.ofDerivable _ _ (equation c)
def table (c : Bool) : List (Rule Rel) := [rule c]
def indices : List Nat := [48]

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.Interchange
