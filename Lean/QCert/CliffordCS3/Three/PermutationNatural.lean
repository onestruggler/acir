/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checked Coxeter calculations in the natural ordering of the basis
-/
import QCert.CliffordCS3.Three.PermutationCert

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QCert.CliffordCS3.Three.PermutationNatural
open ToffoliHadamard

abbrev Letter := Fin 7
def nW : Word Letter →* Word Gen := FreeMonoid.lift fun d =>
  PermutationBase.D (FreeMonoid.ofList (xAdj d))
def NW (l : List Letter) : Word Gen := nW (FreeMonoid.ofList l)

def R : WRel Letter := fun a b => Derivable Rel (nW a) (nW b)

theorem transfer {a b : Word Letter} (h : Derivable R a b) : Derivable Rel (nW a) (nW b) :=
  Derivable.map nW (fun _ _ h => h) h

theorem involution (d : Letter) : Derivable R (FreeMonoid.ofList [d,d]) 1 := by
  apply Derivable.of
  have hp : (xAdj d).reverse = xAdj d := by fin_cases d <;> rfl
  have h := ToffoliHadamard.Engine.mul_reverse PermutationCert.involutions (xAdj d)
  rw [hp] at h
  have hh := PermutationCert.transfer h
  simpa only [R, nW, FreeMonoid.lift_ofList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, FreeMonoid.ofList_append, map_mul, map_one] using hh

theorem far (i j : Letter) (hij : i.val + 2 ≤ j.val) :
    Derivable R (FreeMonoid.ofList [i,j]) (FreeMonoid.ofList [j,i]) := by
  apply Derivable.of
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals first
    | exact PermutationCert.far02
    | exact PermutationCert.far03
    | exact PermutationCert.far04
    | exact PermutationCert.far05
    | exact PermutationCert.far06
    | exact PermutationCert.far13
    | exact PermutationCert.far14
    | exact PermutationCert.far15
    | exact PermutationCert.far16
    | exact PermutationCert.far24
    | exact PermutationCert.far25
    | exact PermutationCert.far26
    | exact PermutationCert.far35
    | exact PermutationCert.far36
    | exact PermutationCert.far46

theorem braid (i : Fin 6) :
    Derivable R (FreeMonoid.ofList [i.castSucc,i.succ,i.castSucc])
      (FreeMonoid.ofList [i.succ,i.castSucc,i.succ]) := by
  apply Derivable.of
  fin_cases i
  · exact PermutationCert.braid0
  · exact PermutationCert.braid1
  · exact PermutationCert.braid2
  · exact PermutationCert.braid3
  · exact PermutationCert.braid4
  · exact PermutationCert.braid5

def squareRule (d : Letter) : Rule R := Rule.ofDerivable _ _ (involution d)
def farRule (i j : Letter) (hij : i.val + 2 ≤ j.val) : Rule R := Rule.ofDerivable _ _ (far i j hij)
def braidRule (i : Fin 6) : Rule R := Rule.ofDerivable _ _ (braid i)

def rules : List (Rule R) := [
  squareRule 0, squareRule 1, squareRule 2, squareRule 3, squareRule 4, squareRule 5, squareRule 6,
  farRule 0 2 (by decide), farRule 0 3 (by decide), farRule 0 4 (by decide), farRule 0 5 (by decide),
  farRule 0 6 (by decide), farRule 1 3 (by decide), farRule 1 4 (by decide), farRule 1 5 (by decide),
  farRule 1 6 (by decide), farRule 2 4 (by decide), farRule 2 5 (by decide), farRule 2 6 (by decide),
  farRule 3 5 (by decide), farRule 3 6 (by decide), farRule 4 6 (by decide),
  braidRule 0, braidRule 1, braidRule 2, braidRule 3, braidRule 4, braidRule 5]

def code (x : Letter) : Nat := x.val + 1
theorem bounds (x : Letter) : 0 < code x ∧ code x < 16 := by dsimp [code]; omega
theorem inj : Function.Injective code := by
  intro a b h; apply Fin.ext; simp only [code] at h; omega

theorem derive (a b : List Letter) (cs : List (Nat × Nat))
    (hc : runChunks (compileRules code rules) cs (enc code a) = some (enc code b)) :
    Derivable Rel (NW a) (NW b) :=
  transfer (derivable_of_chunks bounds inj rules (FreeMonoid.ofList a)
    (FreeMonoid.ofList b) cs hc)

theorem append (a b : List Letter) : NW (a ++ b) = NW a * NW b := by
  simp only [NW, FreeMonoid.ofList_append, map_mul]

end QCert.CliffordCS3.Three.PermutationNatural
