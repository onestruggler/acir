/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The two cosets for three-qubit Clifford+CS

The action is checked through the macro presentation of U₈. Every entry
of the certificate tables is a derivation from Figure 2; the finite
checks below connect their endpoints to the stated action.

Generated data and this proof template are assembled by `finalize3.py`.
-/
import QCert.CliffordCS3.Cert.Targets
import QCert.CliffordCS3.Macro8
import QCert.CliffordCS3.Translation

namespace QCert.CliffordCS3.Cosets

open Macro
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The identity coset (`false`) and the coset of the phase on state 7 (`true`). -/
def action : Bool → ML → Word Gen × Bool
  | false, .Z => (FreeMonoid.ofList [], true)
  | false, .K => (FreeMonoid.ofList [Gen.K₁, Gen.S₀, Gen.S₀, Gen.S₀, Gen.S₁, Gen.S₁, Gen.CS₀₁, Gen.K₁, Gen.S₁, Gen.S₁, Gen.S₂, Gen.S₂, Gen.S₂, Gen.CS₁₂, Gen.K₁, Gen.S₁, Gen.S₁, Gen.CS₀₁, Gen.K₁, Gen.S₁, Gen.S₁, Gen.CS₁₂], true)
  | false, .T 0 => (FreeMonoid.ofList [Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i], false)
  | false, .T 1 => (FreeMonoid.ofList [Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₀, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₀, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i], false)
  | false, .T 2 => (FreeMonoid.ofList [Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i], false)
  | false, .T 3 => (FreeMonoid.ofList [Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i, Gen.K₂, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i], false)
  | false, .T 4 => (FreeMonoid.ofList [Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i, Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i], false)
  | false, .T 5 => (FreeMonoid.ofList [Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i, Gen.K₀, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₀, Gen.i, Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i], false)
  | false, .T 6 => (FreeMonoid.ofList [Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i], false)
  | true, .Z => (FreeMonoid.ofList [Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂], false)
  | true, .K => (FreeMonoid.ofList [Gen.K₁, Gen.S₀, Gen.S₀, Gen.S₀, Gen.S₁, Gen.S₁, Gen.CS₀₁, Gen.K₁, Gen.S₁, Gen.S₁, Gen.S₂, Gen.S₂, Gen.S₂, Gen.CS₁₂, Gen.K₁, Gen.S₁, Gen.S₁, Gen.CS₀₁, Gen.K₁, Gen.S₁, Gen.S₁, Gen.CS₁₂, Gen.K₁, Gen.S₀, Gen.S₀, Gen.S₀, Gen.S₁, Gen.S₁, Gen.CS₀₁, Gen.K₁, Gen.S₁, Gen.S₁, Gen.S₂, Gen.S₂, Gen.S₂, Gen.CS₁₂, Gen.K₁, Gen.S₁, Gen.S₁, Gen.CS₀₁, Gen.K₁, Gen.S₁, Gen.S₁, Gen.CS₁₂, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i], false)
  | true, .T 0 => (FreeMonoid.ofList [Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i], true)
  | true, .T 1 => (FreeMonoid.ofList [Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₀, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₀, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i], true)
  | true, .T 2 => (FreeMonoid.ofList [Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.S₂, Gen.S₂, Gen.K₂, Gen.i, Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i], true)
  | true, .T 3 => (FreeMonoid.ofList [Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i, Gen.K₂, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i], true)
  | true, .T 4 => (FreeMonoid.ofList [Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i, Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₀, Gen.S₀, Gen.S₀, Gen.K₀, Gen.i], true)
  | true, .T 5 => (FreeMonoid.ofList [Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i, Gen.K₀, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₀, Gen.i, Gen.K₁, Gen.S₁, Gen.S₁, Gen.K₁, Gen.i], true)
  | true, .T 6 => (FreeMonoid.ofList [Gen.K₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.CS₀₁, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.i, Gen.K₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₂, Gen.i, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂, Gen.CS₁₂, Gen.CS₁₂, Gen.K₁, Gen.CS₀₁, Gen.CS₀₁, Gen.K₁, Gen.i, Gen.CS₁₂], true)

def b2OK : Bool :=
  M8.D.ax.all fun e => [false, true].all fun c =>
    (hstar action c (FreeMonoid.ofList e.1)).2 ==
        (hstar action c (FreeMonoid.ofList e.2)).2 &&
    Cert.b2Table.any fun t => t.1 == c && t.2.1 == e.1 && t.2.2.1 == e.2 &&
      t.2.2.2.lhs == FreeMonoid.toList (hstar action c (FreeMonoid.ofList e.1)).1 &&
      t.2.2.2.rhs == FreeMonoid.toList (hstar action c (FreeMonoid.ofList e.2)).1

theorem b2OK_true : b2OK = true := by decide +kernel

theorem b2 (c : Bool) (w v : Word ML) (h : MRel M8.D w v) :
    (hstar action c w).2 = (hstar action c v).2 ∧
      Derivable Rel (hstar action c w).1 (hstar action c v).1 := by
  cases h with
  | @ax e he =>
    have hb := b2OK_true
    simp only [b2OK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨hc, t, _, ⟨⟨⟨⟨_, _⟩, _⟩, hl⟩, hr⟩⟩ := hb e he c (by cases c <;> simp)
    refine ⟨hc, ?_⟩
    have ht := t.2.2.2.sound
    rw [hl, hr, FreeMonoid.ofList_toList, FreeMonoid.ofList_toList] at ht
    exact ht

/-- Read a one- or two-level generator through its macro encoding. -/
def hact (c : Bool) (y : BianSelingerUn.Gen 8) : Word Gen × Bool :=
  hstar action c (encW M8.D (FreeMonoid.of y))

theorem hstar_hact (c : Bool) (w : Word (BianSelingerUn.Gen 8)) :
    hstar hact c w = hstar action c (encW M8.D w) := by
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => rfl
  | mul_of y w ih =>
    rw [hstar_mul, hstar_of, map_mul, hstar_mul, ih]
    rfl

def aOK : Bool :=
  [Gen.i, .K₀, .K₁, .K₂, .S₀, .S₁, .S₂, .CS₀₁, .CS₁₂].all fun x =>
    (hstar action false (encW M8.D (fG x))).2 == false &&
    Cert.aTable.any fun t => t.1 == x &&
      t.2.lhs == FreeMonoid.toList (hstar action false (encW M8.D (fG x))).1 &&
      t.2.rhs == [x]

theorem aOK_true : aOK = true := by decide +kernel

theorem hyp_a (x : Gen) : (hstar hact false (fG x)).2 = false ∧
    Derivable Rel (hstar hact false (fG x)).1 (FreeMonoid.of x) := by
  rw [hstar_hact]
  have ha := aOK_true
  simp only [aOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
  obtain ⟨hc, t, _, ⟨⟨_, hl⟩, hr⟩⟩ := ha x (by cases x <;> simp)
  refine ⟨hc, ?_⟩
  have ht := t.2.sound
  rw [hl, hr, FreeMonoid.ofList_toList] at ht
  exact ht

theorem hyp_b (c : Bool) (w v : Word (BianSelingerUn.Gen 8)) (h : BianSelingerUn.Rel 8 w v) :
    (hstar hact c w).2 = (hstar hact c v).2 ∧
      Derivable Rel (hstar hact c w).1 (hstar hact c v).1 := by
  rw [hstar_hact, hstar_hact]
  exact rs_claimB action b2 (M8.b1 w v h) c

end QCert.CliffordCS3.Cosets
