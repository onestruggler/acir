/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The finite obligations of the two-coset table

The endpoint checks below depend only on the parity of the macro letters.
They are separate from the residual word equations, which must be proved
from Figure 2 by the certificate replay.
-/
import QCert.CliffordCS3.Three.Interface
import QCert.CliffordCS3.Three.Cert.Words

namespace QCert.CliffordCS3.Three

open Macro

def decoding : Decoding :=
  ⟨Cert.token, Cert.atom, FreeMonoid.ofList Cert.ccZL⟩

def h : Bool → ML → Word Gen × Bool := action decoding

/-- The pair of residual words of a macro axiom from one coset. -/
def residuals (c : Bool) (e : List ML × List ML) : Word Gen × Word Gen :=
  ((hstar h c (FreeMonoid.ofList e.1)).1, (hstar h c (FreeMonoid.ofList e.2)).1)

def bStatesOK : Bool :=
  [false, true].all fun c => M8.D.ax.all fun e =>
    (hstar h c (FreeMonoid.ofList e.1)).2 == (hstar h c (FreeMonoid.ofList e.2)).2

theorem bStatesOK_true : bStatesOK = true := by decide +kernel

theorem b_states (c : Bool) (e : List ML × List ML) (he : e ∈ M8.D.ax) :
    (hstar h c (FreeMonoid.ofList e.1)).2 = (hstar h c (FreeMonoid.ofList e.2)).2 := by
  have ht := bStatesOK_true
  simp only [bStatesOK, List.all_eq_true, beq_iff_eq] at ht
  exact ht c (by cases c <;> simp) e he

def aStatesOK : Bool :=
  generators.all fun x => (hstar h false (encW M8.D (fG x))).2 == false

theorem aStatesOK_true : aStatesOK = true := by decide +kernel

theorem a_states (x : Gen) : (hstar h false (encW M8.D (fG x))).2 = false := by
  have ht := aStatesOK_true
  simp only [aStatesOK, List.all_eq_true, beq_iff_eq] at ht
  exact ht x (mem_generators x)

end QCert.CliffordCS3.Three
