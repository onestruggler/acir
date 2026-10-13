"""Generate Axioms.agda: the rules C1-C18 as Engine equations."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import re, sys
import agdaparse as ap

SYN = ROOT + '/Syntactics.agda'
OUT = ROOT + '/Axioms.agda'

LET = {('nu',): '𝕟', ('H', 0): 'h₀', ('H', 1): 'h₁', ('H', 2): 'h₂',
       ('S', 0): 's₀', ('S', 1): 's₁', ('S', 2): 's₂',
       ('CZ', 0): 'c₀', ('CZ', 1): 'c₁'}

def agda_list(toks):
    if not toks:
        return '[]'
    return '(' + ' ∷ '.join(LET[t] for t in toks) + ' ∷ [])'

if __name__ != "__main__" and False: pass
src = open(SYN, encoding='utf-8').read()
for line in src.splitlines():
    m = re.match(r'^(\S+)\s+=\s+(.*)$', line)
    if m and m.group(1) not in ('n', 'H', 'S', 'CZ', 'ν'):
        try:
            ap.define(m.group(1), m.group(2))
        except Exception:
            pass

rules = []
for line in src.splitlines():
    m = re.match(r'^\s+(C\S+)\s+:\s+(.*?)QRel,\s+(.*?)\s+===\s+(.*)$', line)
    if m:
        name, width, lhs, rhs = m.groups()
        w = 0
        for k, tag in ((1, '₁₊'), (2, '₂₊'), (3, '₃₊')):
            if tag in width:
                w = k
        assert ap.check(w, lhs, rhs), name
        rules.append((name, w, ap.parse(lhs), ap.parse(rhs)))

WID = {0: 'n', 1: '(₁₊ n)', 2: '(₂₊ n)', 3: '(₃₊ n)'}
out = []
out.append('''------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations C1 … C18 as equations of letter lists (Engine.Eqn),
-- with short names for the letters on the bottom three wires
--
-- Generated from Syntactics by gen_axioms.py: each list is the rule's
-- word with its derived generators unfolded, which by-assoc checks.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Axioms where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

import Presentation.Base as PB
import Presentation.Properties as PP

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (Eqn ; eqn ; ⟪_⟫)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letters: the scalar, and H, S, CZ on the bottom wires

pattern 𝕟  = gate₀ ν-gate
pattern h₀ = gate₁ H-gate
pattern h₁ = gate₁ H-gate ↥
pattern h₂ = gate₁ H-gate ↥ ↥
pattern s₀ = gate₁ S-gate
pattern s₁ = gate₁ S-gate ↥
pattern s₂ = gate₁ S-gate ↥ ↥
pattern c₀ = gate₂ CZ-gate
pattern c₁ = gate₂ CZ-gate ↥

------------------------------------------------------------------------
-- The relations, read up to associativity

private
  ax : ∀ {m} {w v : Circuit m} (l r : List (Gen m)) → m QRel, w === v →
       m ⊢ ⟪ l ⟫ ≈ w → m ⊢ v ≈ ⟪ r ⟫ → Eqn m
  ax l r a p q = eqn l r (PB.trans p (PB.trans (PB.axiom (srel a)) q))

  as : ∀ {m} {w v : Circuit m} → PP.to-list (m VRel,_===_) w Eq.≡ PP.to-list (m VRel,_===_) v →
       m ⊢ w ≈ v
  as {m} = PP.by-assoc (m VRel,_===_)
''')
for name, w, l, r in rules:
    out.append(f'''{name}ᵉ : Eqn {WID[w]}
{name}ᵉ = ax {agda_list(l)}
  {agda_list(r)} {name} (as Eq.refl) (as Eq.refl)
''')
open(OUT, 'w', encoding='utf-8').write('\n'.join(out))
print('wrote', len(rules), 'rules')
