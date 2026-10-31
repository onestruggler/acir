/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The permutation part of the two-coset certificate
-/
import QCert.CliffordCS3.Three.PermutationRoutes
import QCert.CliffordCS3.Three.PhaseDressed
import QCert.CliffordCS3.Three.BasicCases

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.Cert.Permutations

open QuotientGroup LocalKZ
noncomputable section

def tw (c : Bool) (d : Fin 7) : Word Gen :=
  if c && decide (d = 6) then phase * token d * ccZ else token d

theorem square (c : Bool) (d : Fin 7) : Derivable Rel (tw c d * tw c d) 1 := by
  cases c
  · exact token_involution d
  · by_cases hd : d = 6
    · subst d
      apply to_derivable
      change PhaseDressed.U * PhaseDressed.U = 1
      rw [← PhaseDressed.D_dresses]
      have ht : T * T = 1 := by
        simpa only [map_mul, map_one] using of_derivable (token_involution 6)
      calc
        _ = AtomTokens.D * (T * T) * AtomTokens.D⁻¹ := by group
        _ = 1 := by rw [ht]; group
    · simpa only [tw, hd, decide_false, Bool.and_false, Bool.false_eq_true, ite_false] using token_involution d

theorem pure_far (i j : Fin 7) (hij : i.val + 2 ≤ j.val) :
    Derivable Rel (token i * token j) (token j * token i) := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals first
    | exact PermutationRoutes.far02
    | exact PermutationRoutes.far03
    | exact PermutationRoutes.far04
    | exact PermutationRoutes.far05
    | exact PermutationRoutes.far06
    | exact PermutationRoutes.far13
    | exact PermutationRoutes.far14
    | exact PermutationRoutes.far15
    | exact PermutationRoutes.far16
    | exact PermutationRoutes.far24
    | exact PermutationRoutes.far25
    | exact PermutationRoutes.far26
    | exact PermutationRoutes.far35
    | exact PermutationRoutes.far36
    | exact PermutationRoutes.far46

theorem far (c : Bool) (i j : Fin 7) (hij : i.val + 2 ≤ j.val) :
    Derivable Rel (tw c i * tw c j) (tw c j * tw c i) := by
  cases c
  · exact pure_far i j hij
  · have hi : i ≠ 6 := by intro h; subst i; omega
    by_cases hj : j = 6
    · subst j
      have hi5 : i.val < 5 := by omega
      let d : Fin 5 := ⟨i.val, hi5⟩
      have hd : d.castSucc.castSucc = i := Fin.ext rfl
      have hp : Commute T (u (token d.castSucc.castSucc)) := by
        rw [hd]
        simpa only [map_mul] using (of_derivable (pure_far i 6 hij)).symm
      have h := PhaseDressed.dressed_disjoint d hp
      rw [hd] at h
      apply to_derivable
      simpa only [tw, hi, decide_false, Bool.and_false, Bool.false_eq_true, ite_false,
        decide_true, Bool.and_true, Bool.true_eq, ite_true, map_mul] using h.symm.eq
    · simpa only [tw, hi, hj, decide_false, Bool.and_false, Bool.false_eq_true, ite_false] using pure_far i j hij

theorem pure_braid (i : Fin 6) :
    Derivable Rel (token i.castSucc * token i.succ * token i.castSucc)
      (token i.succ * token i.castSucc * token i.succ) := by
  fin_cases i
  · simpa only [PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using PermutationRoutes.braid0
  · simpa only [PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using PermutationRoutes.braid1
  · simpa only [PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using PermutationRoutes.braid2
  · simpa only [PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using PermutationRoutes.braid3
  · simpa only [PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using PermutationRoutes.braid4
  · simpa only [PermutationRoutes.tokens, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_assoc] using PermutationRoutes.braid5

theorem braid (c : Bool) (i : Fin 6) :
    Derivable Rel (tw c i.castSucc * tw c i.succ * tw c i.castSucc)
      (tw c i.succ * tw c i.castSucc * tw c i.succ) := by
  cases c
  · exact pure_braid i
  · by_cases hi : i = 5
    · subst i
      apply to_derivable
      have hp : u (token 5) * T * u (token 5) = T * u (token 5) * T := by
        simpa only [map_mul] using of_derivable (pure_braid 5)
      simpa only [tw, Fin.reduceEq, decide_false, decide_true, Bool.and_false, Bool.and_true,
        Bool.false_eq_true, Bool.true_eq, ite_false, ite_true, map_mul] using PhaseDressed.dressed_braid hp
    · have hj : i.succ ≠ 6 := by intro h; apply hi; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
      have hk : i.castSucc ≠ 6 := by intro h; have := congrArg Fin.val h; simp at this; omega
      simpa only [tw, hj, hk, decide_false, Bool.and_false, Bool.false_eq_true, ite_false] using pure_braid i

def squareRule (c : Bool) (d : Fin 7) : Rule Rel := Rule.ofDerivable _ _ (square c d)
def farRule (c : Bool) (i j : Fin 7) (hij : i.val + 2 ≤ j.val) : Rule Rel := Rule.ofDerivable _ _ (far c i j hij)
def braidRule (c : Bool) (i : Fin 6) : Rule Rel := Rule.ofDerivable _ _ (braid c i)

def table (c : Bool) : List (Rule Rel) :=
  (List.ofFn fun i : Fin 7 => squareRule c i) ++
  (List.ofFn fun i : Fin 6 => braidRule c i) ++
  [farRule c 0 2 (by decide), farRule c 0 3 (by decide), farRule c 0 4 (by decide), farRule c 0 5 (by decide),
   farRule c 0 6 (by decide), farRule c 1 3 (by decide), farRule c 1 4 (by decide), farRule c 1 5 (by decide),
   farRule c 1 6 (by decide), farRule c 2 4 (by decide), farRule c 2 5 (by decide), farRule c 2 6 (by decide),
   farRule c 3 5 (by decide), farRule c 3 6 (by decide), farRule c 4 6 (by decide)]

def indices : List Nat := List.range 28

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.Permutations
