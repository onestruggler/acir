# Agda for the lowered derivations: Four/Letters.agda (the macro letters
# and their spellings) and Four/D/Dnnn.agda, one module per derivation,
# each a chain of segment replacements (Four/Chain) in blocks of eight
# steps between explicit lines.
import sys, os, io, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from mac import mac_tree, agda_of, LITERAL
import deriv
from prim import show
import lower as LW

ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'Four')

SUB = {'0': '0', '1': '1', '2': '2', '3': '3'}
def mname(g):
    k = g[0]; w = ''.join(str(x) for x in g[1:])
    if k == 'iI': return 'ι' + (w if w != '0' else '')
    if k == 'iIi': return 'ι' + (w if w != '0' else '') + '⁻'
    if k in ('Sd', 'Kd', 'CSd', 'CKd'): return k[:-1] + w + '⁻'
    if k == 'SWAP': return 'Sw' + w
    if k == 'TOFF': return 'Toff' + w
    return k + w

def all_letters():
    gates = [('iI', w) for w in range(4)] + [('iIi', w) for w in range(4)]
    for w in range(4):
        for k in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): gates.append((k, w))
    for a in range(4):
        for b in range(4):
            if a == b: continue
            if a < b: gates += [('CS', a, b), ('CSd', a, b), ('CZ', a, b)]
            gates += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
            if b == a + 1: gates.append(('SWAP', a, b))
    for s in ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)): gates.append(('CCZ',) + s)
    for t in range(4):
        cs = [w for w in range(4) if w != t]
        for i in range(3):
            for j in range(i + 1, 3): gates.append(('TOFF', t, cs[i], cs[j]))
    return gates

def expr(g):
    """the Agda expression of a letter (any width), parenthesised."""
    e = agda_of(mac_tree(g))
    return f'({e})' if ' ' in e else e

def word_expr(letters):
    if not letters: return 'ε'
    return ' • '.join(expr(g) for g in letters)

def shifted(g, m):
    """the letter with wire m deleted (wires above m down one)."""
    return deriv.norm([(g[0],) + tuple(w - 1 if w > m else w for w in g[1:])])[0]

def downk(g, i): return deriv.norm([(g[0],) + tuple(w - i for w in g[1:])])[0]

def lst(letters): return '(' + ' ∷ '.join(mname(g) for g in letters) + ' ∷ [])' if letters else '[]'

def lemname(name):
    s = name.replace(' ', '-').replace('=', '≡').replace('[', '').replace(']', '').replace(',', '')
    return 'lem-' + s

# ------------------------------------------------------------ letters
def letters_module():
    out = ['------------------------------------------------------------------------',
           '-- Presentations of groups', '--',
           '-- The macro letters of the four-wire derivations and their spellings', '--',
           '-- A gate on adjacent wires is the lifted basic word; a gate on wires',
           '-- further apart is the gate one wire closer conjugated by the adjacent',
           '-- swap at its top (stacked swaps); a three-wire gate on wires 0 1 2 or',
           '-- 1 2 3 is literal, the other two are conjugates by one swap.  Every',
           '-- spelling is checked against the gate it names by',
           '-- `scratchpad/four/mac.py`; `emit.py` writes this module.',
           '------------------------------------------------------------------------', '',
           '{-# OPTIONS --without-K --safe #-}', '',
           'module Examples.Groups.Clifford+CS.Four.Letters where', '',
           'open import Word.Base using (_•_)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)', '',
           'data Mac : Set where']
    gates = all_letters()
    out.append('  ' + ' '.join(mname(g) for g in gates) + ' : Mac')
    out += ['', '⟪_⟫ : Mac → Circuit 4']
    for g in gates:
        out.append(f'⟪ {mname(g)} ⟫ = {agda_of(mac_tree(g))}')
    return '\n'.join(out) + '\n'

# ------------------------------------------------------------ steps
def step_proof(st):
    kind, k, n, seg, ys, extra = st
    if kind == 'W':
        m = extra; r = 3 - m
        u = word_expr([shifted(g, m) for g in seg]); v = word_expr([shifted(g, m) for g in ys])
        return f'win {m} {r} complete₃ ({u}) ({v}) tt tt Eq.refl'
    if kind == 'C':
        g, h = seg; i, botfirst = extra
        name = {1: 'low₁-comm', 2: 'low-comm', 3: 'low₃-comm'}[i]
        bot, top = (g, h) if botfirst else (h, g)
        t = f'{name} ({word_expr([bot])}) ({word_expr([downk(top, i)])})'
        return t if botfirst else f'sym ({t})'
    if kind == 'R': return 'by-assoc Eq.refl'
    if kind == 'A':
        name, fwd = extra; t = 'ax ' + name
        return t if fwd else f'sym ({t})'
    if kind == 'L':
        name, fwd = extra; t = lemname(name)
        return t if fwd else f'sym {t}'
    raise ValueError(kind)

HEADER = '''{{-# OPTIONS --without-K --safe #-}}

module Examples.Groups.Clifford+CS.Four.D.{mod} where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
{deps}
'''

def derivation_module(P, index, modof, block=8):
    """the Agda module of the primitive derivation P."""
    mod = f'D{index:03d}'
    deps = sorted({extra[0] for (kind, k, n, seg, ys, extra) in P.steps if kind == 'L'})
    dep_lines = '\n'.join(f'open import Examples.Groups.Clifford+CS.Four.D.{modof[d]} using ({lemname(d)})' for d in deps)
    lines = [list(P.lhs)]
    cur = list(P.lhs)
    for (kind, k, n, seg, ys, extra) in P.steps:
        cur = cur[:k] + list(ys) + cur[k + n:]; lines.append(cur)
    assert lines[-1] == list(P.rhs)
    out = [HEADER.format(mod=mod, deps=dep_lines)]
    out.append(f'-- {P.name}: {len(P.steps)} steps (scratchpad/four/lower.py)')
    nm = lemname(P.name)
    nblocks = (len(P.steps) + block - 1) // block
    out.append(f'{nm} : ⟪ {lst(P.lhs)} ⟫ʷ ≈ ⟪ {lst(P.rhs)} ⟫ʷ')
    if nblocks == 0:
        out.append(f'{nm} = refl'); return mod, '\n'.join(out) + '\n'
    runs = [f'run b{b}' for b in range(nblocks)]
    body = runs[-1]
    for r in reversed(runs[:-1]): body = f'trans ({r}) ({body})'
    out.append(f'{nm} = {body}')
    out.append('  where')
    for b in range(nblocks):
        s0, s1 = b * block, min((b + 1) * block, len(P.steps))
        out.append(f'  b{b} : Chain {lst(lines[s0])} {lst(lines[s1])}')
        parts = []
        for i in range(s0, s1):
            kind, k, n, seg, ys, extra = P.steps[i]
            parts.append(f'at {k} {n} {lst(ys)} ({step_proof(P.steps[i])})')
        out.append(f'  b{b} = ' + ' ▸\n       '.join(parts) + ' ▸ done')
        out.append('')
    return mod, '\n'.join(out) + '\n'

def write_all(prims):
    os.makedirs(os.path.join(ROOT, 'D'), exist_ok=True)
    io.open(os.path.join(ROOT, 'Letters.agda'), 'w', encoding='utf-8', newline='\n').write(letters_module())
    modof = {}; mods = []
    for i, P in enumerate(prims, 1):
        mod, text = derivation_module(P, i, modof)
        modof[P.name] = mod; mods.append(mod)
        io.open(os.path.join(ROOT, 'D', mod + '.agda'), 'w', encoding='utf-8', newline='\n').write(text)
    io.open(os.path.join(ROOT, 'D', 'INDEX.txt'), 'w', encoding='utf-8', newline='\n').write(
        '\n'.join(f'{modof[P.name]} {P.name} {len(P.steps)}' for P in prims) + '\n')
    return mods

if __name__ == '__main__':
    import lemmas8
    prims = LW.lower_all(deriv.DERIVATIONS)
    mods = write_all(prims)
    print(len(mods), 'modules written to', ROOT)
