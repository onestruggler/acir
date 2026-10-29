/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two qubits: completeness of the relations on a pair

The relations (a)–(c) of Figure 2 on a pair of qubits (`Rel2`) are complete
for the two-qubit Clifford+CS circuits (`complete2`): by the
Reidemeister–Schreier theorem (`QCert.reidemeister_schreier`) from
Bian–Selinger's presentation of `U₄(ℤ[1/2, i])`
(`QCert.BianSelingerUn.presentation 4`), with one coset.  The coset action
sends a one- or two-level generator to the decoding (`decW`) of its
encoding over the macro alphabet (`M4.D`): hypothesis (b) is the macro
derivation of every relation (`M4.b1`) followed by the decoded macro
axioms (`b2`), hypothesis (a) the decoded encoding of the translation of
each generator (`Cert.aTable`).

`derivable_of_check2`: an equation on a pair that `check2` decides true is
derivable; with `derivable_embed` it is derivable in Figure 2 on either
pair of adjacent qubits.
-/
import QCert.CliffordCS3.Two.Cert.Targets
import QCert.CliffordCS3.Two.Macro4
import QCert.CliffordCS3.Two.Semantics
import QCert.CliffordT2.ReidemeisterSchreier
import QCert.BianSelingerUn.Theorem

namespace QCert.CliffordCS3.Two

open Macro

/-- The decoding of the macro letters of `U₄` as words on a pair. -/
def dec4 : ML → Word Gen2
  | .T d => match d.val with
    | 0 => FreeMonoid.ofList [.i, .Kl, .Sl, .Sl, .CS, .CS, .Kl]
    | 1 => FreeMonoid.ofList [.i, .Ku, .Su, .Su, .CS, .CS, .Ku]
    | 2 => FreeMonoid.ofList [.i, .Kl, .CS, .CS, .Kl]
    | _ => 1
  | .Z => FreeMonoid.of .CS
  | .K => FreeMonoid.ofList [.i, .Su, .Su, .Su, .CS, .Kl, .CS, .Kl, .CS]

/-- The decoding of macro words. -/
def decW : Word ML →* Word Gen2 := FreeMonoid.lift dec4

/-- The decoded macro axioms, checked against the table. -/
def b2OK : Bool :=
  M4.D.ax.all fun e => Cert.b2Table.any fun t =>
    t.1 == e.1 && t.2.1 == e.2 && t.2.2.lhs == FreeMonoid.toList (decW (FreeMonoid.ofList e.1)) &&
      t.2.2.rhs == FreeMonoid.toList (decW (FreeMonoid.ofList e.2))

theorem b2OK_true : b2OK = true := by decide +kernel

/-- B2: every macro axiom decodes to a derivable equation. -/
theorem b2 {u v : Word ML} (h : MRel M4.D u v) : Derivable Rel2 (decW u) (decW v) := by
  cases h with
  | @ax e he =>
  have hb := b2OK_true
  simp only [b2OK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨t, -, ⟨⟨-, -⟩, hl⟩, hr⟩ := hb e he
  have := t.2.2.sound
  rw [hl, hr, FreeMonoid.ofList_toList, FreeMonoid.ofList_toList] at this
  exact this

/-- Macro derivations decode to derivations on a pair. -/
theorem derivable_dec {u v : Word ML} (h : Derivable (MRel M4.D) u v) :
    Derivable Rel2 (decW u) (decW v) := by
  have : conGen (MRel M4.D) ≤ (conGen Rel2).comap decW (fun _ _ => map_mul _ _ _) :=
    Con.conGen_le fun a b hab => b2 hab
  exact this h

/-- The coset action (one coset). -/
def hact : Unit → BianSelingerUn.Gen 4 → Word Gen2 × Unit :=
  fun _ y => (decW (encW M4.D (FreeMonoid.of y)), ())

theorem hstar_hact (w : Word (BianSelingerUn.Gen 4)) :
    hstar hact () w = (decW (encW M4.D w), ()) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of y w ih =>
    rw [hstar_mul, hstar_of, ih]
    simp [hact]

/-- Hypothesis (a), checked against the table. -/
def aOK : Bool :=
  [Gen2.i, .Ku, .Kl, .Su, .Sl, .CS].all fun x => Cert.aTable.any fun t =>
    t.1 == x && t.2.lhs == FreeMonoid.toList (decW (encW M4.D (FreeMonoid.lift f2 (FreeMonoid.of x)))) &&
      t.2.rhs == [x]

theorem aOK_true : aOK = true := by decide +kernel

theorem hyp_a (x : Gen2) : (hstar hact () (f2 x)).2 = () ∧
    Derivable Rel2 (hstar hact () (f2 x)).1 (FreeMonoid.of x) := by
  refine ⟨rfl, ?_⟩
  rw [hstar_hact]
  have hb := aOK_true
  simp only [aOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨t, -, ⟨-, hl⟩, hr⟩ := hb x (by cases x <;> simp)
  have := t.2.sound
  rw [hl, hr, FreeMonoid.ofList_toList, FreeMonoid.lift_eval_of] at this
  exact this

theorem hyp_b (c : Unit) (w w' : Word (BianSelingerUn.Gen 4)) (h : BianSelingerUn.Rel 4 w w') :
    (hstar hact c w).2 = (hstar hact c w').2 ∧
      Derivable Rel2 (hstar hact c w).1 (hstar hact c w').1 := by
  refine ⟨rfl, ?_⟩
  rw [hstar_hact, hstar_hact]
  exact derivable_dec (M4.b1 w w' h)

/-- Completeness on a pair: words with the same value are derivably equal. -/
theorem complete2 (w v : Word Gen2) (h : sem2 w = sem2 v) : Derivable Rel2 w v :=
  reidemeister_schreier hact () f2 hyp_a hyp_b ((BianSelingerUn.presentation 4).complete h)

/-- An equation on a pair decided by `check2` is derivable. -/
theorem derivable_of_check2 {w v : Word Gen2} (h : check2 w v = true) : Derivable Rel2 w v :=
  complete2 w v (sem2_eq_of_check2 h)

end QCert.CliffordCS3.Two
