"""Four's window libraries by tables of letters.

    python3 wintable4.py REPO

Each lemma of Four/Wins/W01-W49 was `win i r b (u) (v) _ _ Eq.refl`, the
two three-wire words spelled out letter by letter: Agda elaborated both
and compared them, through `insʷ i`, with the letters of the lemma's
statement -- about 85 ms a window, two thirds of a library's checking.
This pass reads off each window's words, letter by letter, the word of
every letter at every idle wire (the same wherever the letter occurs,
checked), writes them as tables in Four/Lits.agda (Four.Win.lwin, as
Five.Lits does for Five's windows), and rewrites every lemma as
`lwI b xs ys tt tt Eq.refl` over the lists of its statement.  Run it
after winlib4.py / winmac4.py / winbase.py; a library already rewritten
is read back from the tables.  Idempotent.
"""
import os, re, sys

REPO = sys.argv[1]
NL = '\n'
B = os.path.join(REPO, 'Examples/Groups/Clifford+CS')
WINS = os.path.join(B, 'Four', 'Wins')
PFX = 'Examples.Groups.Clifford+CS.'
LITS = os.path.join(B, 'Four', 'Lits.agda')

SIG = re.compile(r'^(wn\d+) : Base 3 → ⟪ (.*) ⟫ʷ ≈ ⟪ (.*) ⟫ʷ$', re.M)
OLD = re.compile(r'^(wn\d+) b = win (\d) (\d) b (.*) _ _ Eq\.refl$', re.M)
NEW = re.compile(r'^(wn\d+) b = lw(\d) b ')


def args(s):
    # the top-level parenthesised arguments of s, in order
    out, depth, start = [], 0, None
    for k, c in enumerate(s):
        if c == '(':
            if depth == 0: start = k
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0: out.append(s[start + 1:k])
    assert depth == 0, s
    return out


def parts(w):
    # a word written letter by letter, `(u₁) • (u₂) • …`, or `ε`
    if w.strip() == 'ε': return []
    out, depth, cur = [], 0, ''
    k = 0
    while k < len(w):
        c = w[k]
        if c == '(': depth += 1
        elif c == ')': depth -= 1
        if depth == 0 and w.startswith(' • ', k):
            out.append(cur); cur = ''; k += 3; continue
        cur += c; k += 1
    out.append(cur)
    res = []
    for p in out:
        p = p.strip()
        if p.startswith('(') and args(p) == [p[1:-1]] and p.endswith(')'): p = p[1:-1]
        res.append(p)
    return res


def letters(l):
    l = l.strip()
    if l == '[]': return []
    assert l.startswith('(') and l.endswith(' ∷ [])'), l
    return [x.strip() for x in l[1:-len(' ∷ [])')].split(' ∷ ')]


# the tables: from Four/Lits if there, then from every library not yet rewritten
table = {}                               # (i, letter) -> word
if os.path.exists(LITS):
    for i, g, u in re.findall(r'^lit(\d) (\S+) = just \(W\d\.lit \((.*)\) tt Eq\.refl\)$',
                              open(LITS, encoding='utf-8').read(), re.M):
        table[(int(i), g)] = u
libs = sorted(f for f in os.listdir(WINS) if re.fullmatch(r'W\d\d\.agda', f))
srcs = {f: open(os.path.join(WINS, f), encoding='utf-8').read() for f in libs}
iof = {0: 3, 1: 2, 2: 1, 3: 0}
nwin = 0
for f, s in srcs.items():
    sig = {n: (letters(xs), letters(ys), xs, ys) for n, xs, ys in SIG.findall(s)}
    for n, i, r, rest in OLD.findall(s):
        i, r = int(i), int(r)
        assert iof[i] == r, (f, n)
        u, v = args(rest)
        xs, ys = sig[n][0], sig[n][1]
        for ls, w in ((xs, u), (ys, v)):
            ps = parts(w)
            assert len(ps) == len(ls), (f, n, ls, ps)
            for g, p in zip(ls, ps):
                old = table.setdefault((i, g), p)
                assert old == p, (f, n, i, g, old, p)
        nwin += 1
print('harvested', nwin, 'windows,', len(table), 'table entries')

# Four/Lits
out = ['-' * 72,
       '-- Presentations of groups',
       '--',
       '-- The tables of the four-wire windows',
       '--',
       '-- For each idle wire i, the three-wire word of every letter spelled',
       '-- off wire i that a window meets (Four.Win.lwin); `lwI` is a window',
       '-- step with i idle.  Written by `scratchpad/four/wintable4.py`, which',
       '-- read the words off the window libraries.',
       '-' * 72, '',
       '{-# OPTIONS --without-K --safe #-}', '',
       f'module {PFX}Four.Lits where', '',
       'open import Data.Maybe.Base using (Maybe ; just ; nothing)',
       'open import Data.Unit.Base using (tt)',
       'open import Relation.Binary.PropositionalEquality as Eq using ()',
       'open import Word.Base using (_•_)', '',
       f'open import {PFX}Syntactics',
       f'open import {PFX}MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)',
       f'open import {PFX}Four.Letters', '',
       f'import {PFX}Four.Win']
for i in range(4):
    out.append(f'module W{i} = {PFX}Four.Win {i} {iof[i]} Mac ⟪_⟫')
macs = re.search(r'data Mac : Set where\n((?:  .*\n)+)',
                 open(os.path.join(B, 'Four', 'Letters.agda'), encoding='utf-8').read()).group(1)
order = {m: k for k, m in enumerate(x for line in macs.split(NL) for x in line.split(':')[0].split())}
for i in range(4):
    out += ['', f'lit{i} : (g : Mac) → Maybe (W{i}.Lit g)']
    for g in sorted((g for (j, g) in table if j == i), key=lambda g: order[g]):
        out.append(f'lit{i} {g} = just (W{i}.lit ({table[(i, g)]}) tt Eq.refl)')
    out += [f'lit{i} _ = nothing', '', f'lw{i} : _', f'lw{i} = W{i}.lwin lit{i}']
open(LITS, 'w', encoding='utf-8', newline=NL).write(NL.join(out) + NL)

# the libraries
IMPORTS = [f'open import Data.List.Base using ([] ; _∷_)',
           'open import Data.Unit.Base using (tt)',
           'open import Relation.Binary.PropositionalEquality as Eq using ()', '',
           f'open import {PFX}Windows using (Base)',
           f'open import {PFX}Four.Chain using (⟪_⟫ʷ ; _≈_)',
           f'open import {PFX}Four.Letters',
           f'open import {PFX}Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)']
nrew = 0
for f, s in srcs.items():
    sig = {n: (xs, ys) for n, xs, ys in SIG.findall(s)}

    def sub(mm):
        n, i = mm.group(1), mm.group(2)
        xs, ys = sig[n]
        return f'{n} b = lw{i} b {xs} {ys} tt tt Eq.refl'
    new = OLD.sub(sub, s)
    h = re.search(r'^module \S+ where\n', new, re.M)
    first = re.search(r'^wn\d+ : ', new, re.M)
    new = new[:h.end()] + NL + NL.join(IMPORTS) + NL + NL + new[first.start():]
    new = new.replace('-- the same operator, equal by completeness on three wires\n'
                      '-- (Windows.win, one evaluation), stated over the macro letters as\n'
                      '-- Four/D uses it.  Written by scratchpad/four/winlib4.py and restated\n'
                      '-- by winmac4.py.',
                      '-- the same operator, equal by completeness on three wires\n'
                      '-- (Windows.win, one evaluation, through the tables of Four.Lits),\n'
                      '-- stated over the macro letters as Four/D uses it.  Written by\n'
                      '-- scratchpad/four/winlib4.py, restated by winmac4.py and wintable4.py.')
    if new != s:
        open(os.path.join(WINS, f), 'w', encoding='utf-8', newline=NL).write(new)
        nrew += 1
print('Four/Lits:', sum(1 for _ in table), 'entries;', nrew, 'libraries rewritten')
