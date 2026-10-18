# Agda statements of (F4) and (F2) over the generators of the four-wire
# domain, from the lemmas Five/D/* emitted by emit5.py (their modules read
# off Five/D/INDEX.txt):
#   Five/F4.agda   f4 : Ws → (g h : Gen 4) → λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g
#   Five/F2.agda   f2 : Ws → (g h : Gen 4) → T (apart g h) →
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


def imports(names, idx, lemf=None):
    mods = {}
    for n in names:
        mods.setdefault(idx[n], set()).add((lemf or lem)(n))
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
        'open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws)',
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
    s += 'f4 : Ws → (g h : Gen 4) → 5 ⊢ₓ λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g' + NL
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
    s += 'f2 : Ws → (g h : Gen 4) → T (apart g h) → 5 ⊢ₓ λ¹ g • λ¹ h ≈ λ¹ h • λ¹ g' + NL
    s += NL.join(clauses) + NL
    return s


def write(path, s):
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(s)


# ------------------------------------------------------------ (F1)
# (joint name, Agda constructor, arity); lf, hyb-sq, hyb-yb are the schema
RULES = [('order-I', 'order-I', 0), ('order-S', 'order-S', 1), ('order-K', 'order-K', 1),
         ('order-SK', 'order-SK', 1), ('order-CS', 'order-CS', 2),
         ('comm-CS-S0', 'comm-CS-S₀', 2), ('comm-CS-S1', 'comm-CS-S₁', 2),
         ('X-CS0', 'X-CS₀', 2), ('X-CS1', 'X-CS₁', 2), ('CS-K0', 'CS-K₀', 2), ('CS-K1', 'CS-K₁', 2),
         ('comm-CSu-CS', 'comm-CS↑-CS', 3), ('rel-266', 'rel-266', 3), ('rel-267', 'rel-267', 3),
         ('rel-268', 'rel-268', 3), ('rel-269', 'rel-269', 3), ('rel-272', 'rel-272', 3),
         ('cx-ccz', 'cx-ccz', 4), ('toff-ccz', 'toff-ccz', 4), ('ck-tct', 'ck-tct', 4)]
SCHEMA = [('lf', 'ctl-lf'), ('hyb-sq', 'ctl-hsq'), ('hyb-yb', 'ctl-hyb')]
TR = {'(': '⟨', ')': '⟩', '.': '·', '>': '⟶', '|': '∣', ';': '·', '{': '', '}': '', '"': '', ',': '', '@': 'at',
      '^': 'ᵖ', '[': '', ']': '', '=': '≡', ':': '∶'}


def lemname(name):                       # as emit5.lemname
    s = name.replace(' ', '-')
    s = ''.join(TR.get(ch, ch) for ch in s)
    while '--' in s:
        s = s.replace('--', '-')
    return 'lem-' + s


def f1(idx):
    names, out = [], []
    ups = lambda o: ''.join(' ↑' for _ in range(o))
    for o in (0, 1):
        width = 4 - o
        sig = (f'f1{SUB[o]} : Ws → {width} SRel, w === v → '
               f'5 ⊢ₓ λ¹ʷ (w{ups(o)}) ≈ λ¹ʷ (v{ups(o)})' if o else
               'f1₀ : Ws → 4 SRel, w === v → 5 ⊢ₓ λ¹ʷ w ≈ λ¹ʷ v')
        out.append(sig)
        for jn, an, ar in RULES:
            if ar > width:
                continue
            n = f'F1-{jn}@{0 if ar == 0 else o}'
            assert n in idx, f'{n} not derived'
            names.append(n)
            out.append(f'f1{SUB[o]} c4 {an} = {conv(lemname(n) + " c4")}')
        if o == 0:
            for jn, ctl in SCHEMA:
                out.append(f'f1₀ c4 {jn} = PB.axiom (srelₓ ({ctl} 0))')
        out.append('')
    out += ['-- The record Five.Transport takes.',
            'f1 : Ws → F1',
            'f1 c4 = record { f1₀ = f1₀ c4 ; f1₁ = f1₁ c4 ; f1₂ = F1Low.f1₂ c4',
            '               ; f1₃ = F1Low.f1₃ c4 ; f1₄ = F1Low.f1₄ c4 }', '']
    s = head('(F1): the rules of the four-wire theory, controlled',
             ['λ¹ of both sides of every rule of Syntactics at every placement',
              'in the four-wire domain (f1ᵒ: the rule at offset o) are equal on',
              "five wires (the paper's (F1)): the derivations Five.D",
              '(scratchpad/joint/f1.py, f1big.py, deb.py, ckt2.py) from four-wire',
              'windows and, for the items whose controlled K sits on the target of',
              'an S-box, the transports of two-wire equations (Five.TR2); the items',
              "at the offsets 2-4 are Five.F1Low's; the controlled lf, hyb-sq,",
              'hyb-yb are rules of the schema.'],
             f'{MOD}.F1', extra='open import Data.Nat using (ℕ)' + NL + 'import Presentation.Base as PB' + NL)
    s = s.replace('open import Word.Base using (_•_)', 'open import Word.Base using (Word ; _•_)')
    s = s.replace('open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ ; λ¹)',
                  'open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)')
    s = s.replace('open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)',
                  'open import Examples.Groups.Clifford+CS.Five.Rules\n'
                  '  using (_⊢ₓ_≈_ ; srelₓ ; ctl-lf ; ctl-hsq ; ctl-hyb)\n'
                  'open import Examples.Groups.Clifford+CS.Five.Transport using (F1)\n'
                  f'import {MOD}.F1Low as F1Low')
    s += NL.join(imports(sorted(set(names)), idx, lemname)) + NL + NL
    s += 'private\n  variable\n    n : ℕ\n    w v : Word (Gen n)\n\n'
    s += NL.join(out)
    return s


SUB = '₀₁₂₃₄'

if __name__ == '__main__':
    idx = index()
    write(os.path.join(FIVE, 'F4.agda'), f4(idx))
    write(os.path.join(FIVE, 'F2.agda'), f2(idx))
    print('F4.agda, F2.agda written')
    if 'f1' in __import__('sys').argv:
        write(os.path.join(FIVE, 'F1.agda'), f1(idx))
        print('F1.agda written')
