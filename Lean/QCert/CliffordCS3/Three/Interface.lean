/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Finite certificates for the two-coset action

The encoding M8.b1 already proves every U₈ axiom from the macro axioms.
Consequently hypothesis (b) of Reidemeister–Schreier reduces to the two
cosets and the finite list M8.D.ax. Hypothesis (a) reduces to the nine
Clifford+CS generators. Both checks consume derivations, not matrix tests.
-/
import QCert.CliffordCS3.Three.Action
import QCert.CliffordCS3.Macro8
import QCert.CliffordCS3.Translation

namespace QCert.CliffordCS3.Three

open Macro

/-- Run the encoded one- or two-level generator through the macro action. -/
def encodedAction (h : Bool → ML → Word Gen × Bool) :
    Bool → BianSelingerUn.Gen 8 → Word Gen × Bool :=
  fun c y => hstar h c (encW M8.D (FreeMonoid.of y))

theorem hstar_encodedAction (h : Bool → ML → Word Gen × Bool)
    (c : Bool) (w : Word (BianSelingerUn.Gen 8)) :
    hstar (encodedAction h) c w = hstar h c (encW M8.D w) := by
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => simp [hstar_one]
  | mul_of y w ih =>
    rw [hstar_mul, map_mul, hstar_mul, hstar_of]
    simp only [encodedAction, ih]

/-- B2 checks the residuals of every macro axiom from both cosets. -/
def b2OK (h : Bool → ML → Word Gen × Bool) (table : Bool → List (Rule Rel)) : Bool :=
  [false, true].all fun c => M8.D.ax.all fun e =>
    let a := hstar h c (FreeMonoid.ofList e.1)
    let b := hstar h c (FreeMonoid.ofList e.2)
    (a.2 == b.2) && (table c).any fun t =>
      t.lhs == FreeMonoid.toList a.1 && t.rhs == FreeMonoid.toList b.1

theorem b2_of_check (h : Bool → ML → Word Gen × Bool)
    (table : Bool → List (Rule Rel)) (hok : b2OK h table = true)
    (c : Bool) (u v : Word ML) (huv : MRel M8.D u v) :
    (hstar h c u).2 = (hstar h c v).2 ∧
      Derivable Rel (hstar h c u).1 (hstar h c v).1 := by
  cases huv with
  | @ax e he =>
    simp only [b2OK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq] at hok
    have hc := hok c (by cases c <;> simp)
    obtain ⟨hs, t, -, hl, hr⟩ := hc e he
    refine ⟨hs, ?_⟩
    have ht := t.sound
    rw [hl, hr, FreeMonoid.ofList_toList, FreeMonoid.ofList_toList] at ht
    exact ht

/-- The finite macro check implies hypothesis (b) for all U₈ axioms. -/
theorem hyp_b_of_check (h : Bool → ML → Word Gen × Bool)
    (table : Bool → List (Rule Rel)) (hok : b2OK h table = true)
    (c : Bool) (w v : Word (BianSelingerUn.Gen 8)) (hwv : BianSelingerUn.Rel 8 w v) :
    (hstar (encodedAction h) c w).2 = (hstar (encodedAction h) c v).2 ∧
      Derivable Rel (hstar (encodedAction h) c w).1 (hstar (encodedAction h) c v).1 := by
  rw [hstar_encodedAction, hstar_encodedAction]
  exact rs_claimB h (b2_of_check h table hok) (M8.b1 w v hwv) c

def generators : List Gen := [.i, .K₀, .K₁, .K₂, .S₀, .S₁, .S₂, .CS₀₁, .CS₁₂]

theorem mem_generators (x : Gen) : x ∈ generators := by cases x <;> simp [generators]

/-- A checks recovery of each of the nine subgroup generators. -/
def aOK (h : Bool → ML → Word Gen × Bool) (table : List (Rule Rel)) : Bool :=
  generators.all fun x =>
    let r := hstar h false (encW M8.D (fG x))
    (r.2 == false) && table.any fun t =>
      t.lhs == FreeMonoid.toList r.1 && t.rhs == [x]

theorem hyp_a_of_check (h : Bool → ML → Word Gen × Bool)
    (table : List (Rule Rel)) (hok : aOK h table = true) (x : Gen) :
    (hstar (encodedAction h) false (fG x)).2 = false ∧
      Derivable Rel (hstar (encodedAction h) false (fG x)).1 (FreeMonoid.of x) := by
  rw [hstar_encodedAction]
  simp only [aOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨hs, t, -, hl, hr⟩ := hok x (mem_generators x)
  refine ⟨hs, ?_⟩
  have ht := t.sound
  rw [hl, hr, FreeMonoid.ofList_toList] at ht
  exact ht

end QCert.CliffordCS3.Three
