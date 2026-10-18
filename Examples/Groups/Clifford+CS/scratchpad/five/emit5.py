# Agda for the lowered five-wire derivations (lower5.py):
#   Five/Letters.agda  the macro letters (data Mac), the boxes' definitions
#                      and the spelling ⟪_⟫;
#   Five/Lits.agda     the literal-window tables (one per idle wire) and lwᵢ;
#   Five/D/Rnnn.agda   the respelling lemmas and the commutations of letters
#                      covering all five wires (literal windows only);
#   Five/Resps.agda    the placed-window tables and pwᵢ;
#   Five/D/Dnnn.agda   the derivations, chains of segment replacements in
#                      blocks of eight steps between explicit lines.
# Every lemma takes completeness on four wires as its first argument.
#   python3 emit5.py RUN_ALL.pkl [ROOT]
import sys, os, io, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lower5 as L5
import prim5
from prim5 import is_box, is_scalar, norm1, show, spelled, semsupp
import spell5 as S5
from spell5 import mname, box_def_name, letter_expr, word_expr, paren
import derivn

NL = chr(10)
ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(HERE))), 'Clifford+CS', 'Five')
MOD = 'Examples.Groups.Clifford+CS.Five'

def lst(letters): return '(' + ' ∷ '.join(mname(g) for g in letters) + ' ∷ [])' if letters else '[]'

TR = {'(': '⟨', ')': '⟩', '.': '·', '>': '⟶', '|': '∣', ';': '·', '{': '', '}': '', '"': '', ',': '', '@': 'at',
      '^': 'ᵖ', '[': '', ']': '', '=': '≡', ':': '∶'}
def lemname(name):
    s = name.replace(' ', '-')
    s = ''.join(TR.get(ch, ch) for ch in s)
    while '--' in s: s = s.replace('--', '-')
    return 'lem-' + s

# ------------------------------------------------------------ letters
def primitive_letters():
    gates = []
    W = range(5)
    for s in W: gates += [('iI', s), ('iIi', s)]
    for w in W:
        for k in ('S', 'Sd', 'K', 'Kd', 'X', 'Z'): gates.append((k, w))
    for a in W:
        for b in W:
            if a == b: continue
            if a < b: gates += [('CS', a, b), ('CSd', a, b), ('CZ', a, b), ('SWAP', a, b)]
            gates += [('CX', a, b), ('CK', a, b), ('CKd', a, b)]
    for s in itertools.combinations(W, 3):
        gates.append(('CCZ',) + s)
        for t in s:
            c = [w for w in s if w != t]; gates.append(('TOFF', t, c[0], c[1]))
    return [norm1(g) for g in gates]

def box_closure(boxes):
    out = []; seen = set()
    def visit(g):
        if g in seen: return
        seen.add(g)
        for h in derivn.unfold1(g):
            h = norm1(h)
            if is_box(h): visit(h)
        out.append(g)
    for g in sorted(boxes, key=mname): visit(g)
    return out

def letters_module(prims, boxes):
    out = ['------------------------------------------------------------------------',
           '-- Presentations of groups', '--',
           '-- The macro letters of the five-wire derivations and their spellings', '--',
           '-- A gate on wires w₁ < … < wₖ is its literal on the k adjacent wires from',
           '-- w₁, whose upper wires are carried up by conjugation with adjacent',
           '-- swaps, the highest first; a box (Clément\'s box, the S-box and the',
           '-- K-box of the joint paper, and their inverses) is the concatenation of',
           '-- the letters of its one-level unfolding, so that unfolding and folding',
           '-- are definitional.  Every spelling is checked against the gate it',
           '-- names by `scratchpad/five/mac5.py`; `emit5.py` writes this module.',
           '------------------------------------------------------------------------', '',
           '{-# OPTIONS --without-K --safe #-}', '',
           f'module {MOD}.Letters where', '',
           'open import Word.Base using (_•_)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)', '',
           'data Mac : Set where']
    names = [mname(g) for g in prims + boxes]
    assert len(set(names)) == len(names)
    for i in range(0, len(names), 12):
        out.append('  ' + ' '.join(names[i:i + 12]) + ' : Mac')
    out += ['', '-- The boxes, each the concatenation of its one-level unfolding.', '']
    for g in boxes:
        us = [norm1(h) for h in derivn.unfold1(g)]
        out.append(f'{box_def_name(g)} : Circuit 5')
        out.append(f'{box_def_name(g)} = ' + ' • '.join(paren(letter_expr(h)) for h in us))
    out += ['', '⟪_⟫ : Mac → Circuit 5']
    for g in prims + boxes:
        out.append(f'⟪ {mname(g)} ⟫ = {letter_expr(g)}')
    return NL.join(out) + NL

# ------------------------------------------------------------ tables
IR = {0: 4, 1: 3, 2: 2, 3: 1, 4: 0}

def lit_entries(prims, i):
    out = []
    for g in prims:
        if i in spelled(g): continue
        u = S5.letter_expr(S5.shift_down(g, i))
        out.append((g, u))
    return out

def lits_module(prims):
    out = ['------------------------------------------------------------------------',
           '-- Presentations of groups', '--',
           '-- The literal-window tables of the five-wire derivations', '--',
           '-- For each idle wire i, the letters spelled off i with the four-wire',
           '-- word they are the placement of (Five.Win.Lit); lwᵢ is the literal',
           '-- window with wire i idle.  Written by `scratchpad/five/emit5.py`.',
           '------------------------------------------------------------------------', '',
           '{-# OPTIONS --without-K --safe #-}', '',
           f'module {MOD}.Lits where', '',
           'open import Data.Maybe using (Maybe ; just ; nothing)',
           'open import Data.Unit using (tt)',
           'open import Relation.Binary.PropositionalEquality as Eq using ()',
           'open import Word.Base using (_•_)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)',
           f'open import {MOD}.Letters', '']
    out.append(f'import {MOD}.Win')
    for i in range(5):
        out.append(f'module W{i} = {MOD}.Win {i} {IR[i]} Mac ⟪_⟫')
    for i in range(5):
        out += ['', f'lit{i} : (g : Mac) → Maybe (W{i}.Lit g)']
        for g, u in lit_entries(prims, i):
            out.append(f'lit{i} {mname(g)} = just (W{i}.lit ({u}) tt Eq.refl)')
        out.append(f'lit{i} _ = nothing')
        out += ['', f'lw{i} : _', f'lw{i} = W{i}.lwin lit{i}']
    return NL.join(out) + NL

def resps_module(prims, respell, modof):
    deps = {}
    for (g, m), name in respell.items(): deps.setdefault(modof[name], []).append(lemname(name))
    out = ['------------------------------------------------------------------------',
           '-- Presentations of groups', '--',
           '-- The placed-window tables of the five-wire derivations', '--',
           '-- For each idle wire i, the letters that avoid it with a four-wire word',
           '-- u and ⟪ g ⟫ ≈ place i u (Five.Win.Resp): a letter spelled off i by',
           '-- its literal entry, one spelled across i by its respelling lemma',
           '-- (Five.D.R*: the letter wrapped in the swaps of the cycle that place',
           '-- conjugates by); pwᵢ is the placed window with wire i idle.  Written by',
           '-- `scratchpad/five/emit5.py`.',
           '------------------------------------------------------------------------', '',
           '{-# OPTIONS --without-K --safe #-}', '',
           f'module {MOD}.Resps where', '',
           'open import Data.Maybe using (Maybe ; just ; nothing)',
           'import Data.Maybe as Maybe',
           'open import Relation.Binary.PropositionalEquality as Eq using ()',
           'open import Word.Base using (_•_)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)',
           'open import Examples.Groups.Clifford+CS.Completeness using (Complete)',
           f'open import {MOD}.Chain',
           f'open import {MOD}.Lits']
    for m in sorted(deps):
        out.append(f'open import {MOD}.D.{m} using ({" ; ".join(sorted(deps[m]))})')
    for i in range(5):
        out += ['', f'resp{i} : Complete 4 → (g : Mac) → Maybe (W{i}.Resp g)']
        for (g, m), name in sorted(respell.items(), key=lambda kv: mname(kv[0][0])):
            if m != i: continue
            u = S5.letter_expr(S5.shift_down(g, i))
            out.append(f'resp{i} c4 {mname(g)} = just (W{i}.resp ({u}) (trans ({lemname(name)} c4) (by-assoc Eq.refl)))')
        out.append(f'resp{i} c4 g = Maybe.map W{i}.fromLit (lit{i} g)')
        out += ['', f'pw{i} : (c4 : Complete 4) → _', f'pw{i} c4 = W{i}.pwin (resp{i} c4) c4']
    return NL.join(out) + NL

# ------------------------------------------------------------ steps
def step_proof(st):
    kind, k, n, seg, ys, info = st
    if kind == 'W': return f'lw{info} c4 {lst(seg)} {lst(ys)} tt tt Eq.refl'
    if kind == 'P': return f'pw{info} c4 {lst(seg)} {lst(ys)} tt tt Eq.refl'
    if kind == 'C':
        g, h = seg; i, botfirst = info
        bot, top = (g, h) if botfirst else (h, g)
        t = f'c{"₁₂₃₄"[i - 1]} ({letter_expr(bot, False)}) ({letter_expr(S5.downk(top, i), False)})'
        return t if botfirst else f'sym ({t})'
    if kind == 'Z':
        g, h = seg; first = info
        sc = g if first else h
        t = 'zc' if sc[0] == 'iI' else 'zc⁻'
        return f'sym {t}' if first else t
    if kind == 'R': return 'refl' if info in ('unfold', 'fold') else 'by-assoc Eq.refl'
    if kind == 'U': return f'uₛ ({word_expr(seg)}) ({word_expr(ys)}) Eq.refl'
    if kind == 'A':
        name, fwd = info
        if name == 'AX':
            return 'axAX' if fwd else 'sym axAX'
        assert name.startswith('TR2-'), name
        t = f'{lemname(name)} c4'
        return t if fwd else f'sym ({t})'
    if kind == 'L':
        name, fwd = info; t = f'{lemname(name)} c4'
        return t if fwd else f'sym ({t})'
    raise ValueError(kind)

HEADER = '''{{-# OPTIONS --without-K --safe #-}}

module {mod} where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import {MOD}.Chain
open import {MOD}.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
{resps}{deps}
'''

def lemma_text(P, block=8):
    lines = [list(P.lhs)]; cur = list(P.lhs)
    for (kind, k, n, seg, ys, extra) in P.steps:
        cur = cur[:k] + list(ys) + cur[k + n:]; lines.append(cur)
    assert lines[-1] == list(P.rhs), P.name
    out = [f'-- {P.name}: {len(P.steps)} steps']
    nm = lemname(P.name)
    nblocks = (len(P.steps) + block - 1) // block
    out.append(f'{nm} : Complete 4 → ⟪ {lst(P.lhs)} ⟫ʷ ≈ ⟪ {lst(P.rhs)} ⟫ʷ')
    if nblocks == 0:
        out.append(f'{nm} c4 = refl'); return NL.join(out) + NL
    runs = [f'run b{b}' for b in range(nblocks)]
    body = runs[-1]
    for r in reversed(runs[:-1]): body = f'trans ({r}) ({body})'
    out.append(f'{nm} c4 = {body}')
    out.append('  where')
    for b in range(nblocks):
        s0, s1 = b * block, min((b + 1) * block, len(P.steps))
        out.append(f'  b{b} : Chain {lst(lines[s0])} {lst(lines[s1])}')
        parts = []
        for i in range(s0, s1):
            kind, k, n, seg, ys, extra = P.steps[i]
            parts.append(f'at {k} {n} {lst(ys)} ({step_proof(P.steps[i])})')
        out.append(f'  b{b} = ' + (' ▸' + NL + '       ').join(parts) + ' ▸ done')
        out.append('')
    return NL.join(out) + NL

class Part:
    def __init__(self, name, lhs, rhs, steps):
        self.name, self.lhs, self.rhs, self.steps = name, list(lhs), list(rhs), steps

# The heap a derivation needs follows its letter-steps, the length of the
# word each step rewrites summed over its steps, since Agda keeps every
# intermediate word of a module's chains (branch clifford-cs: 45k of them
# peaked at 4.3 GB, 89k over the long words of the de-borrowing went past
# 7.7 GB).  So a derivation is cut into parts of at most COST letter-steps
# (as well as at most `size` steps), and a module holds at most COST of
# them and at most MOD_BYTES of text.
COST = int(os.environ.get('COST', 30_000))
MOD_BYTES = {'R': 100_000, 'D': int(os.environ.get('D_BYTES', 120_000))}

def letter_steps(P):
    cur = list(P.lhs); c = 0
    for (kind, k, n, seg, ys, extra) in P.steps:
        c += len(cur); cur = cur[:k] + list(ys) + cur[k + n:]
    return c

def split_long(prims, limit=1000, size=500):
    out = []
    for P in prims:
        if len(P.steps) <= limit and letter_steps(P) <= COST: out.append(P); continue
        lines = [list(P.lhs)]; cur = list(P.lhs)
        for (kind, k, n, seg, ys, extra) in P.steps:
            cur = cur[:k] + list(ys) + cur[k + n:]; lines.append(cur)
        cuts, c = [0], 0
        for i in range(len(P.steps)):
            w = len(lines[i])
            if i > cuts[-1] and (i - cuts[-1] >= size or c + w > COST):
                cuts.append(i); c = 0
            c += w
        cuts.append(len(P.steps))
        parts = [Part(f'{P.name} part{i}', lines[s0], lines[s1], P.steps[s0:s1])
                 for i, (s0, s1) in enumerate(zip(cuts, cuts[1:]))]
        main = []; cur = list(P.lhs)
        for Q in parts:
            main.append(('L', 0, len(cur), list(cur), list(Q.rhs), (Q.name, True))); cur = list(Q.rhs)
        out += parts + [Part(P.name, P.lhs, P.rhs, main)]
    return out

def uses_tr(P):
    return any(st[0] == 'A' and st[5][0].startswith('TR2-') for st in P.steps)

def chunks(prims, prefix):
    # a module that uses the transports (Five.TR2) starts a new module:
    # Five.TR2 rests on the (F1) items derived before the first of them
    budget = MOD_BYTES[prefix]
    out = []; cur = []; size = 0; cost = 0; tr_seen = False
    for P in prims:
        brk = uses_tr(P) and not tr_seen
        if brk: tr_seen = True
        n = len(lemma_text(P)); c = letter_steps(P)
        if cur and (brk or size + n > budget or cost + c > COST):
            out.append(cur); cur = []; size = 0; cost = 0
        cur.append(P); size += n; cost += c
    if cur: out.append(cur)
    return out

def write_group(prims, prefix, modof, start, uses_resps):
    mods = []
    for i, group in enumerate(chunks(prims, prefix), start):
        mod = f'{prefix}{i:03d}'
        names = {P.name for P in group}
        deps = sorted({extra[0] for P in group for (kind, k, n, seg, ys, extra) in P.steps
                       if kind == 'L' and extra[0] not in names})
        bymod = {}
        for dname in deps: bymod.setdefault(modof[dname], []).append(lemname(dname))
        dep_lines = NL.join(f'open import {MOD}.D.{m} using ({" ; ".join(ns)})' for m, ns in sorted(bymod.items()))
        trs = sorted({lemname(extra[0]) for P in group for (kind, k, n, seg, ys, extra) in P.steps
                      if kind == 'A' and extra[0].startswith('TR2-')})
        if trs:
            dep_lines += NL + f'open import {MOD}.TR2 using ({" ; ".join(trs)})'
        resps = f'open import {MOD}.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)' + NL if uses_resps else ''
        text = HEADER.format(mod=f'{MOD}.D.{mod}', MOD=MOD, deps=dep_lines, resps=resps) + NL.join(lemma_text(P) for P in group)
        for P in group: modof[P.name] = mod
        mods.append((mod, sum(len(P.steps) for P in group)))
        io.open(os.path.join(ROOT, 'D', mod + '.agda'), 'w', encoding='utf-8', newline=NL).write(text)
    return mods

def write_all(prims, respell, root=None):
    global ROOT
    if root: ROOT = root
    os.makedirs(os.path.join(ROOT, 'D'), exist_ok=True)
    for f in os.listdir(os.path.join(ROOT, 'D')):
        if f.endswith('.agda'): os.remove(os.path.join(ROOT, 'D', f))
    pre = [P for P in prims if P.name.startswith('resp ') or P.name.startswith('comm ')]
    main = [P for P in prims if not (P.name.startswith('resp ') or P.name.startswith('comm '))]
    for P in pre:
        assert all(st[0] != 'P' for st in P.steps), P.name
    pre, main = split_long(pre), split_long(main)
    seen = {}
    for P in pre + main:
        n = lemname(P.name); assert n not in seen, ('name clash', P.name, seen.get(n)); seen[n] = P.name
    letters = set()
    for P in prims:
        cur = list(P.lhs); letters |= set(cur)
        for st in P.steps: letters |= set(st[3]) | set(st[4])
    base = primitive_letters()
    extra = sorted((g for g in letters if not is_box(g) and g not in base), key=mname)
    boxes = box_closure({g for g in letters if is_box(g)})
    prims_l = base + extra
    io.open(os.path.join(ROOT, 'Letters.agda'), 'w', encoding='utf-8', newline=NL).write(letters_module(prims_l, boxes))
    io.open(os.path.join(ROOT, 'Lits.agda'), 'w', encoding='utf-8', newline=NL).write(lits_module(prims_l))
    modof = {}
    rmods = write_group(pre, 'R', modof, 1, False)
    io.open(os.path.join(ROOT, 'Resps.agda'), 'w', encoding='utf-8', newline=NL).write(resps_module(prims_l, respell, modof))
    dmods = write_group(main, 'D', modof, 1, True)
    io.open(os.path.join(ROOT, 'D', 'INDEX.txt'), 'w', encoding='utf-8', newline=NL).write(
        NL.join(f'{modof[P.name]} {len(P.steps)} {P.name}' for P in pre + main) + NL)
    # each distinct window once, in Five/Wins (branch clifford-cs's winlib5.py)
    import winlib5
    libs, nw = winlib5.main(ROOT, [])
    print(nw, 'distinct windows in', len(libs), 'library modules')
    return rmods, dmods, len(boxes)

if __name__ == '__main__':
    names = L5.load(sys.argv[1])
    for nm in names: L5.instance(nm, {})
    root = sys.argv[2] if len(sys.argv) > 2 else None
    rmods, dmods, nb = write_all(L5.PRIMS, L5.RESPELL, root)
    print(len(rmods), 'R modules,', len(dmods), 'D modules,', nb, 'boxes, written to', root or ROOT)
