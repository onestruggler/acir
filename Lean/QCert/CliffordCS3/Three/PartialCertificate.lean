/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The currently certified part of the coset table

Every entry contains a derivation from Figure 2. This partial table does
not assert the full Reidemeister--Schreier data: the uncovered macro
equations must still be supplied before rsData can be constructed.
-/
import QCert.CliffordCS3.Three.BasicCases
import QCert.CliffordCS3.Three.Cert.LocalBlock

namespace QCert.CliffordCS3.Three.PartialCertificate

open Macro

def identityRules : List (Rule Rel) :=
  List.ofFn fun d : Fin 6 =>
    Rule.ofDerivable (Cert.token d.castSucc) (Cert.token d.castSucc) (Derivable.refl _)

def table (c : Bool) : List (Rule Rel) :=
  tokenRules ++ Cert.LocalBlock.table c ++ if c then [] else identityRules

def indices (c : Bool) : List ℕ :=
  [0, 1, 2, 3, 4, 5] ++ Cert.LocalBlock.indices ++
    if c then [] else [28, 30, 32, 34, 36, 38]

def covers : Bool :=
  [false, true].all fun c => (indices c).all fun i =>
    let e := M8.D.ax[i]!
    let a := hstar h c (FreeMonoid.ofList e.1)
    let b := hstar h c (FreeMonoid.ofList e.2)
    (a.2 == b.2) && (table c).any fun r =>
      r.lhs == a.1.toList && r.rhs == b.1.toList

theorem covers_true : covers = true := by decide +kernel

/-- Every advertised entry supplies its actual derivation, not only a state check. -/
theorem proved (c : Bool) (i : ℕ) (hi : i ∈ indices c) :
    let e := M8.D.ax[i]!
    let a := hstar h c (FreeMonoid.ofList e.1)
    let b := hstar h c (FreeMonoid.ofList e.2)
    a.2 = b.2 ∧ Derivable Rel a.1 b.1 := by
  have ht := covers_true
  simp only [covers, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq] at ht
  have hc := ht c (by cases c <;> simp)
  obtain ⟨hs, r, -, hl, hr⟩ := hc i hi
  refine ⟨hs, ?_⟩
  have hp := r.sound
  rw [hl, hr, FreeMonoid.ofList_toList, FreeMonoid.ofList_toList] at hp
  exact hp

theorem covered_count : (indices false).length + (indices true).length = 34 := by decide

end QCert.CliffordCS3.Three.PartialCertificate

