#!/usr/bin/env python3
"""Write NaturalP/FourWire/Classical/Circuit.agda: the circuit of each
placed letter (`φL`, the letters other than the adjacent ones by their
definitions, w · b · rev w with w a word in adjacent swaps) and a
derivation in NaturalP, with the schema, of every relator of the tower
(`rel-φ`):

* a relator whose circuit lies on wires 0 1 2 (or 1 2 3) is decided on
  three wires (Kit.fast₃) and widened (or moved up a wire);
* an involution, or a definition, is a palindrome, closed by
  Kit.inv-right after re-bracketing;
* a commutation of letters on disjoint wires covering all four is
  Circuit.Base's comm-gate lemmas and Kit.comm-close;
* the Toffoli-CNOT commutator on four wires is the rule CCX-comm, and
  the Toffoli moved up a wire is the swap rule σ-nat₃.

    python3 -B emit_circuit4.py
"""
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import tower4 as T
from emit_gamma4 import AG

ROOT = HERE.parents[1] / 'NaturalP' / 'FourWire' / 'Classical'
MOD = 'Examples.Groups.CCX+HH.NaturalP.FourWire.Classical'
DEFS = T.definitions()
BASE = {'X': 'S.X', 'CX': 'S.CX', 'HH': 'S.HH', 'SW': 'S.σ', 'CCX': 'S.CCX'}


def up(e, k):
    return e if k == 0 else '(' + e + ' S.↑' * k + ')'


def atom(g, shift):
    """The circuit of a primitive letter, `shift` wires lower, as one
    expression (XC for the reversed CNOT)."""
    l = T.LETTERS[g]
    if l[0] == 'X':
        return up('S.X', l[1] - shift)
    if l[0] == 'CX':
        c, t = l[1], l[2]
        return up('S.CX', t - shift) if c == t + 1 else up('S.XC', c - shift)
    if l[0] == 'SW':
        return up('S.σ', l[1] - shift)
    return up('S.CCX', l[1] - shift)


def tree(es):
    """Right-nested product of expressions (no trailing ε)."""
    if len(es) == 1:
        return es[0]
    return f'{es[0]} • ({tree(es[1:])})' if len(es) > 2 else f'{es[0]} • {es[1]}'


def image(g, shift=0):
    if g in DEFS:
        return '(' + tree([image(h, shift) for h in DEFS[g]]) + ')'
    return atom(g, shift)


def listword(r, shift):
    """⟪ r ⟫'s image: φL r1 • (φL r2 • (… • ε))."""
    out = 'ε'
    for g in reversed(r):
        out = f'{image(g, shift)} • ({out})'
    return out


def wires(g):
    return set(T.wires(T.LETTERS[g]))


def low_arity(g):
    k = T.LETTERS[g][0]
    return {'X': 1, 'CX': 2, 'SW': 2, 'CCX': 3}[k]


def comm_proof(a, b):
    """A • B ≈ B • A for primitives a (at the bottom) and b above it
    (Circuit.Base states the commutations with the shifted word first)."""
    k = low_arity(a)
    bexpr = atom(b, k)              # b, k wires lower
    lem = {1: 'S.comm-gate₁-w↑', 2: 'S.comm-gate₂-w↑↑', 3: 'S.comm-gate₃-w↑↑↑'}[k]
    l = T.LETTERS[a]
    gate = {'X': 'S.X-gate', 'SW': 'S.SW-gate', 'CCX': 'S.CCX-gate'}.get(l[0])
    if gate is None:
        c, t = l[1], l[2]
        if c == t + 1:
            gate = 'S.CX-gate'
        else:
            h = f'PB.sym ({lem} S.HH-gate {bexpr})'
            x = f'PB.sym ({lem} S.CX-gate {bexpr})'
            return f'comm-• ({h}) (comm-• ({x}) ({h}))'
    return f'PB.sym ({lem} {gate} {bexpr})'


def proof(r):
    sup = T.image_support(r, DEFS)
    is_inv = len(r) == 2 and r[0] == r[1]
    is_def = len(r) > 1 and r[0] in DEFS and tuple(r[1:]) == DEFS[r[0]]
    if is_inv or is_def:
        return f'PB.trans (ba Eq.refl) (inv-right (φL {AG[r[0]]}))'
    if sup <= {0, 1, 2}:
        return f'S.widen 1 (fast₃ ({listword(r, 0)}) ε Eq.refl)'
    if sup <= {1, 2, 3}:
        w = listword(r, 1)
        return f'S.lemma-cong↑ ({w}) ε (fast₃ ({w}) ε Eq.refl)'
    if len(r) == 4 and r[0] == r[2] and r[1] == r[3] and not (wires(r[0]) & wires(r[1])):
        a, b = r[0], r[1]
        A, B = f'(φL {AG[a]})', f'(φL {AG[b]})'
        if 0 in wires(a):
            ab = comm_proof(a, b)
        else:
            ab = f'PB.sym ({comm_proof(b, a)})'
        return f'PB.trans (ba Eq.refl) (comm-close {A} {B} ({ab}))'
    names = ' '.join(T.NAME[g] for g in r)
    if names == 'CCX1;23 CX1>0 CCX1;23 CX1>0 SW01 CCX1;23 SW01':
        return ('PB.trans (ba Eq.refl) (PB.trans (PB.cong (PB.axiom (S.srel (S.srel (S.np NP.CCX-comm)))) PB.refl)\n'
                '    (inv-right (S.σ • ((S.CCX S.↑) • S.σ))))')
    if names == 'SW01 SW12 SW23 CCX0;12 SW23 SW12 SW01 CCX1;23':
        return ('PB.trans (ba Eq.refl) (conj-close S.CCX S.σ[ 3 ] (S.CCX S.↑)\n'
                '    (PB.axiom (S.srel (S.σrel (S.σ-nat₃ S.CCX-gate)))))')
    raise ValueError(names)


def main():
    rels = T.relators_tower()
    out = ['''------------------------------------------------------------------------
-- Presentations of groups
--
-- The placed classical letters as circuits, and every relator of the
-- tower derived in NaturalP with the schema on four wires.
--
-- `φL` is the circuit of a letter: the adjacent ones are gates (the
-- reversed CNOT is XC), the others their definitions w · b · rev w,
-- w a word in adjacent swaps.  `rel-φ` derives every relator: on three
-- wires by Kit.fast₃, an involution or a definition as a palindrome, a
-- commutation by Circuit.Base's comm-gate lemmas, and the two rules on
-- four wires, CCX-comm and σ-nat₃ at the Toffoli.
--
-- Generated by Rules/w4/emit_circuit4.py; do not edit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}
''',
           f'module {MOD}.Circuit where\n',
           '''open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.CCX+HH.NaturalP.Syntactics as NP
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Kit
  using (fast₃ ; inv ; inv-right ; comm-close ; conj-close ; comm-•)
open import ''' + MOD + '''.Gamma
''']
    out.append('φL : L → S.Circuit 4')
    for g, a in enumerate(AG):
        out.append(f'φL {a} = {image(g)}')
    out.append('''
φ : Word L → S.Circuit 4
φ = φL ʷ

private
  ba : {w v : S.Circuit 4} → PP.to-list (4 S.VRel,_===_) w ≡ PP.to-list (4 S.VRel,_===_) v →
       4 S.⊢ w ≈ v
  ba = PP.by-assoc (4 S.VRel,_===_)
''')
    out.append('rel-φ : ∀ r → 4 S.⊢ φ ⟪ relator r ⟫ ≈ ε')
    for j, r in enumerate(rels):
        out.append(f'rel-φ r{j} = {proof(r)}')
    (ROOT / 'Circuit.agda').write_text('\n'.join(out) + '\n', encoding='utf-8')
    print('wrote', ROOT / 'Circuit.agda', len(rels), 'relators')


if __name__ == '__main__':
    main()
