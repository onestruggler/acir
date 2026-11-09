"""Writes BaseComm.agda: the three base commutations of bc_results.json
(BC211, BC31, BC4) as PlacedEngine derivations.

Each says that Ḡ = X₃ CX₃₀ X₃ commutes with Q CX₃₀ Q⁻¹ for a base
circuit Q of CLabels (baseQ ₂, ₃, ₄).  The derivations were found by
gen/bc_targets.py with the equations of Equations4 as lemmas, expanded
into rule (7) and three-wire steps, so they are written exactly as
mk_equations4 writes its own.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from mk_equations4 import emit  # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), 'BaseComm.agda')

NAMES = {
    'BC211': ('BC211⁼', [
        "Ḡ against G placed by CCX_{2,0→1} (union type 2 + 1 + 1)."]),
    'BC31': ('BC31⁼', [
        "Ḡ against G placed by CCX_{2,0→1} CCX_{1,0→2} (union type 3 + 1)."]),
    'BC4': ('BC4⁼', [
        "Ḡ against G placed by CX_{0→1} CCX_{1,0→2} (union type 4)."]),
}

HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- The three base commutations of the controlled matchings
--
-- Ḡ = X₃ CX₃₀ X₃ is X on wire 0 controlled by wire 3 = 0, and Q CX₃₀ Q⁻¹,
-- for a circuit Q of the lower wires, is the matching Q μ₀ Q⁻¹
-- controlled by wire 3 = 1.  They act on disjoint halves of the
-- states, so they commute; CRel needs this for one Q of each of the
-- five union types of the matching with μ₀ (CLabels' baseQ).  Two of
-- them are three-wire identities (CBC); the other three, written here,
-- are derivations of PlacedEngine whose steps are rule (7) under a
-- relabelling of the wires and three-wire steps justified by
-- completeness on three wires, found by gen/bc_targets.py with the
-- equations of Equations4 as lemmas (gen/bc_results.json) and written
-- out by gen/mk_basecomm.py.  A letter CCX_{a,b→t} is the Toffoli with
-- controls a, b and target t.  Wire 0 is the bottom wire, and words
-- are in diagram order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.BaseComm where

open import Data.List.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ)
open import Examples.Groups.XCXCCX-4bit.PlacedEngine
'''


def main():
    d = json.load(open(os.path.join(HERE, 'bc_results.json'), encoding='utf-8'))
    tg = {t['name']: t for t in d['targets']}
    parts = [HDR]
    for n in ('BC211', 'BC31', 'BC4'):
        t = tg[n]
        assert t['found'] and t['check'] == 'ok', n
        nm, cm = NAMES[n]
        parts.append(emit(nm, cm, t))
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n\n'.join(parts) + '\n')
    print('wrote', OUT)


if __name__ == '__main__':
    main()
