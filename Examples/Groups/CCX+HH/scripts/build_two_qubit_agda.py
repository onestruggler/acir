#!/usr/bin/env python3
"""Emit the finite HH two-wire Clément/Schreier table and state proofs."""

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DATA = json.loads((ROOT / "two_qubit_schreier.json").read_text(encoding="utf8"))
FINS = ["₀", "₁", "₂", "₃"]


def circuit(word):
    gates = ["X", "(X ↑)", "CX", "HH"]
    return " • ".join(gates[g] for g in word) if word else "ε"


HEADER = """------------------------------------------------------------------------
-- The exact three-coset Schreier table for X,CX,HH on two wires.
-- Generated from two_qubit_schreier.json by build_two_qubit_agda.py.
-- The state obligations below are Agda proofs, not external certificates.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.TwoQubit.Table where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (s≤s)
open import Data.Product.Base using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary.Decidable using (recompute)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base using (Word ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
open import Examples.Groups.CCX+HH.Encoding using (e)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Schreier as Schreier

data Coset : Set where
  c0 c1 c2 : Coset

emit : Coset → T.Gen 4 → Circuit 2
"""


def generator_pattern(g):
    kind, levels = g["gate"], g["levels"]
    if kind == "M":
        return f"T.M-gen {FINS[levels[0]]}"
    if kind == "X":
        return f"T.X-gen {FINS[levels[0]]} {FINS[levels[1]]} p"
    return "T.K-gen a b c d p q r"


MIDDLE = """
-- Remaining X cases have impossible order proofs; the total fallback
-- keeps the table definition independent of proof irrelevance.
emit _ (T.X-gen _ _ _) = ε

step : Coset → T.Gen 4 → Coset
step c0 (T.M-gen _) = c1
step c1 (T.M-gen _) = c0
step c2 (T.M-gen _) = c2
step c (T.X-gen _ _ _) = c
step c0 (T.K-gen _ _ _ _ _ _ _) = c0
step c1 (T.K-gen _ _ _ _ _ _ _) = c2
step c2 (T.K-gen _ _ _ _ _ _ _) = c1

h : Coset → T.Gen 4 → Circuit 2 × Coset
h c g = emit c g , step c g

module Theory = Schreier 2 Coset c0 h
open Theory public using (decode ; state ; _===_ ; _≈_ ; roundtrip ; translated)

state-roundtrip : (g : Gen 2) → c0 ≡ state c0 (e g)
state-roundtrip (gate₀ ())
state-roundtrip X-gen = refl
state-roundtrip CX-gen = refl
state-roundtrip HH-gen = refl
state-roundtrip ((gate₀ ()) ↥)
state-roundtrip (X-gen ↥) = refl
state-roundtrip (((gate₀ ()) ↥) ↥)

full4 : (a b c d : Fin 4) → a < b → b < c → c < d →
          a ≡ ₀ × b ≡ ₁ × c ≡ ₂ × d ≡ ₃
"""


AFTER_FULL = """
full4 ₀ ₁ ₂ ₃ _ _ _ = refl , refl , refl , refl

no-outside : (a b c d e : Fin 4) → b < c → c < d → d < e →
               a ≢ b → a ≢ c → a ≢ d → a ≢ e → ⊥
no-outside a b c d e p q r ab ac ad ae with full4 b c d e p q r
no-outside ₀ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ab refl
no-outside ₁ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ac refl
no-outside ₂ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ad refl
no-outside ₃ .₀ .₁ .₂ .₃ p q r ab ac ad ae | refl , refl , refl , refl = ae refl

state-relations : ∀ c {u v} → u T.=== v → state c u ≡ state c v
"""


def impossible(bound):
    result = "()"
    for _ in range(bound):
        result = f"(s≤s {result})"
    return result


def generate():
    text = HEADER
    for c, row in enumerate(DATA["schreier_table"]):
        for g, cell in zip(DATA["auxiliary_generators"], row):
            text += f"emit c{c} ({generator_pattern(g)}) = {circuit(cell['word'])}\n"
            expected = ((1, 0, 2)[c] if g["gate"] == "M" else
                        (0, 2, 1)[c] if g["gate"] == "K" else c)
            assert cell["state"] == expected
    text += MIDDLE
    for position in range(3):
        for lower in range(4):
            for upper in range(lower + 1):
                variables = ["_", "_", "_", "_"]
                variables[position:position + 2] = [FINS[lower], FINS[upper]]
                proofs = ["_", "_", "_"]
                proofs[position] = impossible(upper)
                text += "full4 " + " ".join(variables + proofs) + "\n"
    text += AFTER_FULL
    arities = {"r1a": 1, "r1b": 0, "r1c": 3,
               "r2a": 6, "r2b": 3, "r2c": 12, "r2d": 1,
               "r2f": 22, "r3a": 3, "r3b": 3, "r3c": 1,
               "r3d": 5, "r3e": 6, "r3f": 6, "r3g": 5,
               "r4a": 4, "r4b": 3, "r4c": 4, "r5a": 7, "r6a": 8}
    for name, arity in arities.items():
        pat = "T." + name + " _" * arity
        if arity:
            pat = "(" + pat + ")"
        for c in range(3):
            text += f"state-relations c{c} {pat} = refl\n"
    text += """state-relations z (T.r2e {b = b} {c = c} {d = d} {e = e} {a = a} p q r ab ac ad ae) =
  ⊥-elim (no-outside a b c d e (recompute (b FP.<? c) p)
    (recompute (c FP.<? d) q) (recompute (d FP.<? e) r) ab ac ad ae)

open Theory.Complete state-roundtrip state-relations public using (encoded-completeness)
"""
    out = ROOT / "TwoQubit" / "Table.agda"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text, encoding="utf8")
    print("Generated HH two-qubit table: 33 entries and exact state-obligation proofs.")


if __name__ == "__main__":
    generate()
