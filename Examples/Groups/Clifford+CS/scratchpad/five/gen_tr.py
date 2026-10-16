# Agda for the transports TR2 of the five-wire derivations (joint/tr.py),
# after emit5.py has written Five/D:
#   Five/F1Low.agda  the (F1) items at the offsets 2, 3, 4 (the rules of at
#                    most two wires on the domain wires 2, 3), from Five.D;
#   Five/TR2.agda    each TR2 axiom: the equation of two circuits u, v on
#                    two wires, decided on their matrices, carried to
#                    `λ¹ʷ (u ↑ ↑) ≈ λ¹ʷ (v ↑ ↑)` by Five.Transport.Low
#                    (completeness on two wires, then rule by rule through
#                    F1Low), and respelled in the letters of Five.Letters.
#   python3 gen_tr.py RUN_ALL.pkl
import sys, os, io, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'joint'))
from prim5 import norm
from spell5 import mname
import gen_lam
import tr

FIVE = gen_lam.FIVE
MOD = gen_lam.MOD
NL = '\n'


def lst(letters):
    return '(' + ' ∷ '.join(mname(g) for g in letters) + ' ∷ [])' if letters else '[]'


GEN2 = {('S', 2): 'S-gen', ('S', 3): 'S-gen ↥', ('K', 2): 'K-gen', ('K', 3): 'K-gen ↥',
        ('CS', 2): 'CS-gen', ('I',): 'I-gen'}


def word2(gs):
    """a canonical word on the wires 2, 3 as a circuit on two wires."""
    if not gs:
        return 'ε'
    return ' • '.join(f'[ {GEN2[g]} ]ʷ' for g in gs)


def f1low(idx):
    names, out = [], []
    ups = lambda o: ''.join(' ↑' for _ in range(o))
    for o in (2, 3, 4):
        width = 4 - o
        out.append(f'f1{gen_lam.SUB[o]} : Complete 4 → ∀ {{w v}} → {width} SRel, w === v → '
                   f'5 ⊢ₓ λ¹ʷ (w{ups(o)}) ≈ λ¹ʷ (v{ups(o)})')
        for jn, an, ar in gen_lam.RULES:
            if ar > width:
                continue
            n = f'F1-{jn}@{0 if ar == 0 else o}'
            assert n in idx, f'{n} not derived'
            names.append(n)
            out.append(f'f1{gen_lam.SUB[o]} c4 {an} = {gen_lam.conv(gen_lam.lemname(n) + " c4")}')
        out.append('')
    s = gen_lam.head('(F1) on the top two domain wires',
                     ['λ¹ of both sides of every rule of at most two wires, placed on the',
                      'domain wires 2, 3 (offsets 2, 3, 4), are equal on five wires: the',
                      '(F1) items that the transport of a two-wire equation meets',
                      '(Five.Transport.Low), from the derivations Five.D.'],
                     f'{MOD}.F1Low', extra='open import Data.Nat using (ℕ)' + NL)
    s = s.replace('open import Word.Base using (_•_)', 'open import Word.Base using (Word ; _•_)')
    s = s.replace('open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ ; λ¹)',
                  'open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)')
    s += NL.join(gen_lam.imports(sorted(set(names)), idx, gen_lam.lemname)) + NL + NL
    s += NL.join(out)
    return s


def tr2(trs, axioms):
    out = []
    for nm, u, v in trs:
        l, r = axioms[nm]
        assert (l, r) == (norm(tr.l1(u)), norm(tr.l1(v))), nm
        ln = gen_lam.lemname(nm)
        out += [f'{ln} : Complete 4 → ⟪ {lst(l)} ⟫ʷ ≈ ⟪ {lst(r)} ⟫ʷ',
                f'{ln} c4 = trans (by-assoc Eq.refl)',
                f'  (trans (tr c4 ({word2(u)}) ({word2(v)}) Eq.refl) (by-assoc Eq.refl))', '']
    s = NL.join([
        '------------------------------------------------------------------------',
        '-- Presentations of groups',
        '--',
        '-- The transported two-wire equations of the five-wire derivations',
        '--',
        '-- Each TR2 axiom of joint/tr.py: two circuits u, v on two wires with',
        '-- the same matrix (one evaluation) are equal by completeness on two',
        '-- wires, and so are their controlled versions on the domain wires 2, 3',
        '-- (Five.Transport.Low, through the (F1) items of Five.F1Low); the sides',
        '-- are then respelled in the letters of the derivations.  Written by',
        '-- scratchpad/five/gen_tr.py.',
        '------------------------------------------------------------------------',
        '',
        '{-# OPTIONS --without-K --safe #-}',
        '',
        f'module {MOD}.TR2 where',
        '',
        'open import Data.List using (List ; [] ; _∷_)',
        'open import Relation.Binary.PropositionalEquality as Eq using ()',
        'open import Word.Base using ([_]ʷ ; ε ; _•_)',
        '',
        'open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)',
        'open import Examples.Groups.Clifford+CS.Completeness using (Complete ; complete₂)',
        'open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; module Below)',
        'open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)',
        'open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)',
        'open import Examples.Groups.Clifford+CS.Five.Transport using (module Low)',
        f'open import {MOD}.F1Low using (f1₂ ; f1₃ ; f1₄)',
        f'open import {MOD}.Chain',
        '',
        'private',
        '  module S₂ = Below 2 complete₂',
        '',
        '  tr : Complete 4 → (u v : Circuit 2) → Same u v → 5 ⊢ₓ λ¹ʷ (u ↑ ↑) ≈ λ¹ʷ (v ↑ ↑)',
        '  tr c4 u v e = Low.transport² c4 (f1₂ c4) (f1₃ c4) (f1₄ c4) (S₂.by-sem₀ u v e)',
        ''] + out)
    return s


if __name__ == '__main__':
    D = pickle.load(open(sys.argv[1], 'rb'))
    axioms = {n: (norm(l), norm(r)) for n, (l, r) in D['L'].items() if n.startswith('TR2-')}
    idx = gen_lam.index()
    for path, text in (('F1Low.agda', f1low(idx)), ('TR2.agda', tr2(D['TRS'], axioms))):
        io.open(os.path.join(FIVE, path), 'w', encoding='utf-8', newline=NL).write(text)
    print('F1Low.agda, TR2.agda written,', len(D['TRS']), 'transports')
