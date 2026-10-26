"""Letter lists as strings, in the derivation modules of Four/D or Five/D.

    python3 strings.py REPO Four|Five [--wins]

Writes TREE/Str.agda -- `ℓ s`, the list of the macro letters the
characters of s stand for, the n-th letter of Mac being U+4E00 + n -- and
rewrites every list of letters `(A ∷ B ∷ … ∷ [])` in TREE/D/*.agda as
`(ℓ "…")`: in the lemmas' statements, the derivations' sides, the
re-bracketing steps and the local equations.  A string is one token,
where a list was a chain of `_∷_` for the operator parser and a term per
letter for the elaborator.  The statements must be spelled alike
wherever they meet: di.py builds the statement trees (DStmt, Four's
CStmt) from the lemmas' signatures, so run it after this pass, and run
this pass again after reflect4.py / reflect5.py regenerate a module.
Also imports Data.List.Base and Data.Unit.Base rather than the umbrella
modules.  Idempotent.
"""
import os, re, sys

REPO, TREE = sys.argv[1], sys.argv[2]
NL = '\n'
B = os.path.join(REPO, 'Examples/Groups/Clifford+CS', TREE)
PFX = 'Examples.Groups.Clifford+CS.'
STR = PFX + TREE + '.Str'
BASE_CHAR = 0x4E00

letters = open(os.path.join(B, 'Letters.agda'), encoding='utf-8').read()
decl = re.search(r'data Mac : Set where\n((?:  .*\n)+)', letters).group(1)
macs = [x for line in decl.split(NL) if line.strip() for x in line.split(':')[0].split()]
code = {m: chr(BASE_CHAR + i) for i, m in enumerate(macs)}
assert all(c not in '"\\' for c in code.values())

w = max(len(m) for m in macs)
out = ['-' * 72,
       '-- Presentations of groups',
       '--',
       f'-- Lists of {"four" if TREE == "Four" else "five"}-wire macro letters as strings',
       '--',
       '-- `ℓ s` is the list of the macro letters the characters of s stand',
       '-- for, the n-th letter of Mac being U+4E00 + n.  The derivation modules',
       f'-- of {TREE}/D and the statement trees spell their letter lists this way:',
       '-- a string is one token, where a list of letters was a chain of `_∷_`',
       '-- for the operator parser and a term per letter for the elaborator.',
       '-- Written by `scratchpad/four/strings.py`, which rewrites the lists.',
       '-' * 72, '',
       '{-# OPTIONS --without-K --safe #-}', '',
       f'module {STR} where', '',
       'open import Agda.Builtin.Char using (Char)',
       'open import Agda.Builtin.List using (List ; [] ; _∷_)',
       'open import Agda.Builtin.String using (String ; primStringToList)', '',
       f'open import {PFX}{TREE}.Letters', '',
       'chM : Char → Mac']
out += [f"chM '{code[m]}' = {m}" for m in macs]
out += [f'chM _   = {macs[0]}', '',
        'private',
        '  dec : List Char → List Mac',
        '  dec []       = []',
        '  dec (c ∷ cs) = chM c ∷ dec cs', '',
        'ℓ : String → List Mac',
        'ℓ s = dec (primStringToList s)']
open(os.path.join(B, 'Str.agda'), 'w', encoding='utf-8', newline=NL).write(NL.join(out) + NL)

LIST = re.compile(r'\(((?:[^\s()∷"]+ ∷ )+)\[\]\)')
REFL = re.compile(r'^(open import ' + re.escape(PFX + TREE) + r'\.Reflect using \([^)]*\)\n)', re.M)
IMPORT = f'open import {STR} using (ℓ)\n'


def enc(mm):
    items = [x.strip() for x in mm.group(1).split('∷') if x.strip()]
    if not all(x in code for x in items):
        return mm.group(0)
    return '(ℓ "' + ''.join(code[x] for x in items) + '")'


n_files = n_lists = 0
DDIR = os.path.join(B, 'D')
paths = [os.path.join(DDIR, f) for f in sorted(os.listdir(DDIR)) if f.endswith('.agda')]
# With --wins, also the window statements (TREE/WinSig) and the window
# libraries (TREE/Wins), which must be spelled alike: TREE/WinInst
# compares each library's lemma with its statement in WinSig, and a
# string against a list would be compared by unfolding the letters.
WINS = '--wins' in sys.argv[3:]
if WINS:
    WDIR = os.path.join(B, 'Wins')
    paths += [os.path.join(B, 'WinSig.agda')]
    paths += [os.path.join(WDIR, f) for f in sorted(os.listdir(WDIR)) if f.endswith('.agda')]
for p in paths:
    f = os.path.relpath(p, B)
    s = open(p, encoding='utf-8').read()
    new, k = LIST.subn(enc, s)
    n_lists += sum(1 for _ in re.finditer(r'\(ℓ "', new)) - sum(1 for _ in re.finditer(r'\(ℓ "', s))
    if IMPORT not in new and '(ℓ "' in new:
        if REFL.search(new):
            new = REFL.sub(lambda mm: mm.group(1) + IMPORT, new, count=1)
        else:
            last = list(re.finditer(r'^open import .*\n', new, re.M))[-1]
            new = new[:last.end()] + IMPORT + new[last.end():]
        assert IMPORT in new, f
    new = new.replace('open import Data.List using (List ; [] ; _∷_)\n',
                      'open import Data.List.Base using (List ; [] ; _∷_)\n')
    new = new.replace('open import Data.Unit using (tt)\n', 'open import Data.Unit.Base using (tt)\n')
    if new != s:
        open(p, 'w', encoding='utf-8', newline=NL).write(new)
        n_files += 1
print(TREE, len(macs), 'letters;', n_files, 'modules rewritten,', n_lists, 'lists')
