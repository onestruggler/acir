# Agda statements of (F4) and (F2) over the generators of the four-wire
# domain, from the lemmas Five/D/* emitted by emit5.py (their modules read
# off Five/D/INDEX.txt):
#   Five/F4.agda   f4 : Complete 4 → (g h : Gen 4) → λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g
#   Five/F2.agda   f2 : Complete 4 → (g h : Gen 4) → T (apart g h) →
#                       λ¹ g • λ¹ h ≈ λ¹ h • λ¹ g
#   python3 gen_lam.py
import os
HERE = os.path.dirname(os.path.abspath(__file__))
FIVE = os.path.join(os.path.dirname(os.path.dirname(HERE)), 'Five')
MOD = 'Examples.Groups.Clifford+CS.Five'
NL = '\n'

# the sixteen generators of Gen 4: (Agda pattern, joint name, wires)
GENS = []
for k in range(5):
    GENS.append(('I-gen' + ' ↥' * k, 'I', set()))
for v in range(4):
    GENS.append(('S-gen' + ' ↥' * v, f'S{v}', {v}))
for v in range(4):
    GENS.append(('K-gen' + ' ↥' * v, f'K{v}', {v}))
for v in range(3):
    GENS.append(('CS-gen' + ' ↥' * v, f'CS{v}', {v, v + 1}))

# the joint scripts' generator order (f4.GENS)
ORDER = ['I'] + [f'S{v}' for v in range(4)] + [f'K{v}' for v in range(4)] + [f'CS{v}' for v in range(3)]


def index():
    out = {}
    for line in open(os.path.join(FIVE, 'D', 'INDEX.txt'), encoding='utf-8'):
        p = line.split()
        if len(p) >= 3:
            out[' '.join(p[2:])] = p[0]
    return out


def lem(name):
    return 'lem-' + name


def imports(names, idx):
    mods = {}
    for n in names:
        mods.setdefault(idx[n], set()).add(lem(n))
    return [f'open import {MOD}.D.{m} using ({" ; ".join(sorted(mods[m]))})' for m in sorted(mods)]


def head(title, body, mod, extra=''):
    return NL.join([
        '------------------------------------------------------------------------',
        '-- Presentations of groups',
        '--',
        f'-- {title}',
        '--'] + [f'-- {l}' for l in body] + [
        '------------------------------------------------------------------------',
        '',
        '{-# OPTIONS --without-K --safe #-}',
        '',
        f'module {mod} where',
        '',
        'open import Relation.Binary.PropositionalEquality as Eq using ()',
        extra + 'open import Word.Base using (_•_)',
        '',
        'open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)',
        'open import Examples.Groups.Clifford+CS.Completeness using (Complete)',
        'open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ ; λ¹)',
        'open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)',
        'open import Examples.Groups.Clifford+CS.Five.Chain',
        ''])


def conv(e):
    return f'trans (by-assoc Eq.refl) (trans ({e}) (by-assoc Eq.refl))'


def f4(idx):
    names, clauses = [], []
    for pg, ng, _ in GENS:
        for ph, nh, _ in GENS:
            n = f'F4-{ng}-{nh}'
            names.append(n)
            clauses.append(f'f4 c4 ({pg}) ({ph}) = {conv(lem(n) + " c4")}')
    s = head('(F4): the two halves of the controlled functor commute',
             ['λ⁰ g and λ¹ h commute on five wires for any two generators g, h of',
              'the four-wire domain (the paper\'s (F4)): the derivations Five.D',
              '(scratchpad/joint/f4.py, f4cs.py), from four-wire windows only.'],
             f'{MOD}.F4')
    s += NL.join(imports(sorted(set(names)), idx)) + NL + NL
    s += 'f4 : Complete 4 → (g h : Gen 4) → 5 ⊢ₓ λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g' + NL
    s += NL.join(clauses) + NL
    return s


def f2(idx):
    names, clauses, apart = [], [], []
    for pg, ng, wg in GENS:
        for ph, nh, wh in GENS:
            apart.append(f'apart ({pg}) ({ph}) = {"false" if wg & wh else "true"}')
            if wg & wh:
                clauses.append(f'f2 c4 ({pg}) ({ph}) ()')
            elif ng == nh:
                clauses.append(f'f2 c4 ({pg}) ({ph}) _ = refl')
            else:
                a, b = (ng, nh) if ORDER.index(ng) < ORDER.index(nh) else (nh, ng)
                n = f'F2-{a}-{b}'
                names.append(n)
                e = conv(lem(n) + ' c4')
                clauses.append(f'f2 c4 ({pg}) ({ph}) _ = ' + (e if (a, b) == (ng, nh) else f'sym ({e})'))
    s = head('(F2): controlled gates on disjoint wires commute',
             ['λ¹ g and λ¹ h commute on five wires for generators g, h of the',
              'four-wire domain on disjoint wires (the paper\'s (F2)): the',
              'derivations Five.D (scratchpad/joint/f2.py), from four-wire windows',
              'and, for the two disjoint CS gates, the five-wire rule AX.'],
             f'{MOD}.F2', extra='open import Data.Bool using (Bool ; true ; false ; T)' + NL)
    s += NL.join(imports(sorted(set(names)), idx)) + NL + NL
    s += '-- Two generators on disjoint wires (the scalar is disjoint from all).' + NL
    s += 'apart : Gen 4 → Gen 4 → Bool' + NL + NL.join(apart) + NL + NL
    s += 'f2 : Complete 4 → (g h : Gen 4) → T (apart g h) → 5 ⊢ₓ λ¹ g • λ¹ h ≈ λ¹ h • λ¹ g' + NL
    s += NL.join(clauses) + NL
    return s


def write(path, s):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(s)


if __name__ == '__main__':
    idx = index()
    write(os.path.join(FIVE, 'F4.agda'), f4(idx))
    write(os.path.join(FIVE, 'F2.agda'), f2(idx))
    print('F4.agda, F2.agda written')
