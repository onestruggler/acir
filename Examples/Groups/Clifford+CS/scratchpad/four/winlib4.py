# Decide each distinct window of the four-wire derivations once.
#
# A window step of Four/D is `(win I R complete₃ (U) (V) tt tt Eq.refl)`:
# two words on three wires with the same operator, decided by one
# evaluation (`Same`, Windows.win).  The derivations use some 136,000 of
# them, of which about 2,600 are distinct, and each module decided its
# own: in a module of 114 window steps (15 distinct) that was half its
# checking time.  This names each distinct window once, as a lemma of a
# library module Four/Wins/Wnn (`wnNNNNN`, its `T` evidence left to `_`,
# which the typecheck-efficiency notes measured faster than `tt`), and
# puts the name in place of the step; a derivation module imports the
# names it uses.  Like repack.py, it changes no derivation otherwise.
#
#   python3 winlib4.py REPO_ROOT [CAP]          (after emit.py, repack.py)
import os, re, sys, collections

ROOT = sys.argv[1]
CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 60_000
C = os.path.join(ROOT, 'Examples', 'Groups', 'Clifford+CS')
D = os.path.join(C, 'Four', 'D')
WD = os.path.join(C, 'Four', 'Wins')
NL = '\n'
mods = sorted(f[:-5] for f in os.listdir(D) if re.fullmatch(r'D\d+\.agda', f))


def windows(s):
    """the window terms of a text, with their spans"""
    out, i = [], 0
    while True:
        j = s.find('(win ', i)
        if j < 0: return out
        d, k = 0, j
        while True:
            c = s[k]
            if c == '(': d += 1
            elif c == ')':
                d -= 1
                if d == 0: break
            k += 1
        out.append((j, k + 1, s[j:k + 1]))
        i = k + 1


def split2(s):
    s = s.strip(); d = 0
    for k, c in enumerate(s):
        if c == '(': d += 1
        elif c == ')':
            d -= 1
            if d == 0: return s[:k + 1], s[k + 1:].strip()
    raise ValueError(s[:60])


texts, name, order = {}, {}, []
for m in mods:
    s = open(os.path.join(D, m + '.agda'), encoding='utf-8').read()
    texts[m] = s
    for _, _, t in windows(s):
        if t not in name:
            mm = re.fullmatch(r'\(win (\d+) (\d+) complete₃ (.*) tt tt Eq\.refl\)', t, re.S)
            assert mm, t[:80]
            name[t] = f'wn{len(name) + 1:05d}'
            order.append((t, mm.group(1), mm.group(2)) + split2(mm.group(3)))

# The library, in modules of at most CAP bytes.
os.makedirs(WD, exist_ok=True)
for f in os.listdir(WD):
    if re.fullmatch(r'W\d+\.agda', f): os.remove(os.path.join(WD, f))
head = ['------------------------------------------------------------------------',
        '-- Presentations of groups', '--',
        '-- Windows of the four-wire derivations, each decided once', '--',
        '-- Each lemma is one window step of Four/D: two words on three wires with',
        '-- the same operator, equal by completeness on three wires',
        '-- (Windows.win, one evaluation).  Written by scratchpad/four/winlib4.py.',
        '------------------------------------------------------------------------', '',
        '{-# OPTIONS --without-K --safe #-}', '']
imports = ['open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)',
           'open import Relation.Binary.PropositionalEquality as Eq using ()',
           'open import Word.Base using (ε ; _•_)', '',
           'open import Notations using (₁₊)', '',
           'open import Examples.Groups.Clifford+CS.Syntactics',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)',
           'open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)',
           'open import Examples.Groups.Clifford+CS.Completeness using (complete₃)', '']
libs, cur, size = [], [], 0
for w in order:
    lines = [f'{name[w[0]]} : (₁₊ ({w[1]} +ℕ {w[2]})) ⊢ insʷ {w[1]} {w[3]} ≈ insʷ {w[1]} {w[4]}',
             f'{name[w[0]]} = win {w[1]} {w[2]} complete₃ {w[3]} {w[4]} _ _ Eq.refl']
    b = sum(len(l.encode('utf-8')) + 1 for l in lines)
    if cur and size + b > CAP:
        libs.append(cur); cur, size = [], 0
    cur.append((name[w[0]], lines)); size += b
if cur: libs.append(cur)
where = {}
for i, ws in enumerate(libs):
    lib = f'W{i + 1:02d}'
    for n, _ in ws: where[n] = lib
    with open(os.path.join(WD, lib + '.agda'), 'w', encoding='utf-8', newline=NL) as f:
        f.write(NL.join(head + [f'module Examples.Groups.Clifford+CS.Four.Wins.{lib} where', ''] + imports
                        + [l for _, ls in ws for l in ls]) + NL)

# The derivation modules: names in place of the windows, and their imports.
for m in mods:
    s, ws = texts[m], windows(texts[m])
    if not ws: continue
    out, i, used = [], 0, set()
    for j, k, t in ws:
        out += [s[i:j], name[t]]; used.add(name[t]); i = k
    out.append(s[i:])
    s = ''.join(out)
    by = collections.defaultdict(list)
    for n in sorted(used): by[where[n]].append(n)
    imp = NL.join(f'open import Examples.Groups.Clifford+CS.Four.Wins.{l} using ({" ; ".join(by[l])})' for l in sorted(by))
    anchor = 'open import Examples.Groups.Clifford+CS.Four.Chain\n'
    assert anchor in s, m
    s = s.replace(anchor, anchor + imp + NL, 1)
    if 'complete₃' not in s.split(anchor, 1)[1]:
        s = s.replace('open import Examples.Groups.Clifford+CS.Completeness using (complete₃)\n', '', 1)
    if not re.search(r'\bwin\b', s.split(anchor, 1)[1]):
        s = s.replace('open import Examples.Groups.Clifford+CS.Windows using (win)\n', '', 1)
    with open(os.path.join(D, m + '.agda'), 'w', encoding='utf-8', newline=NL) as f:
        f.write(s)
print(f'{sum(len(windows(texts[m])) for m in mods)} window steps, {len(name)} distinct, in {len(libs)} library modules')
