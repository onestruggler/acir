# Turn Four/D's chains into derivations by reflection, over a light import
# closure:
#
#   python3 reflect4.py REPO
#
# The last post-pass after emit.py, repack.py and winlib4.py, run on the
# chain form (`bN : Chain … ; bN = at k n ys proof ▸ … ▸ done`).  It writes
#
#   * Four/Reflect.agda, the engine: a derivation is a list of steps
#     checked by running it (`derive l r steps Eq.refl`), each step a
#     rewrite by an equation of the module's table (`rw k q`, `rw⁻ k q`)
#     or a re-bracketing (`re k n ys`, the two spelling the same
#     generators);
#   * Four/WinSig.agda, the windows' statements over the macro letters
#     (each window has one spelling in Four/D) in a balanced tree, `Ws`
#     a tree of their proofs and `wn n W` the n-th (records of the
#     windows, as Five.WinSig has, made a 6.4 MB interface that took
#     100 s and 7 GB to check, against which this is 0.6 MB), and
#     Four/WinInst.agda, the tree of proofs built from Four/Wins;
#   * every module of Four/D, parameterised by the proofs (W : Ws): its
#     distinct equations once each, as a private table `qN = eqn seg ys
#     proof`, and each lemma `derive L R steps Eq.refl`; it imports no
#     module that reaches completeness on three wires (the windows come
#     through W, the structural commutations from LowComm), so loading
#     its imports costs a few seconds instead of twenty;
#   * the modules outside Four/D that import it, applied to WinInst.ws.
#
# Lemma names, statements and INDEX.txt are unchanged.
import os, re, sys, collections

REPO = sys.argv[1]
T = os.path.join(REPO, 'Examples/Groups/Clifford+CS')
D = os.path.join(T, 'Four/D')
P = 'Examples.Groups.Clifford+CS.'


def rd(p):
    return open(p, encoding='utf-8').read()


def wr(p, s):
    open(p, 'w', encoding='utf-8', newline='\n').write(s)


def balanced(s, i):
    d = 0
    for k in range(i, len(s)):
        c = s[k]
        if c == '(':
            d += 1
        elif c == ')':
            d -= 1
            if d == 0:
                return k + 1
    raise ValueError(s[i:i + 80])


def letters(t):
    t = t.strip()
    if t == '[]':
        return []
    assert t[0] == '(' and t.endswith('∷ [])'), t[:80]
    return [x.strip() for x in t[1:-len('∷ [])')].split(' ∷ ') if x.strip()]


def lst(xs):
    return '[]' if not xs else '(' + ' ∷ '.join(xs) + ' ∷ [])'


def chains(text):
    """(start letters, [(k, n, ys, proof)]) for each `bN : Chain (..) (..)` block"""
    out = []
    for m in re.finditer(r'^  (b\d+) : Chain ', text, re.M):
        i = m.end()
        j = balanced(text, i) if text[i] == '(' else i + 2
        start = letters(text[i:j])
        dm = re.search(r'^  ' + m.group(1) + r' = ', text[j:], re.M)
        p = j + dm.end()
        steps = []
        while True:
            while text[p] in ' \n':
                p += 1
            if text.startswith('done', p):
                break
            mm = re.match(r'at (\d+) (\d+) ', text[p:])
            assert mm, text[p:p + 80]
            p += mm.end()
            if text.startswith('[]', p):
                ys, p = [], p + 2
            else:
                q = balanced(text, p)
                ys = letters(text[p:q])
                p = q
            while text[p] == ' ':
                p += 1
            q = balanced(text, p) if text[p] == '(' else p + len(re.match(r'\S+', text[p:]).group(0))
            proof = text[p:q]
            p = q
            steps.append((int(mm.group(1)), int(mm.group(2)), ys, proof))
            while text[p] in ' \n':
                p += 1
            assert text.startswith('▸', p), text[p:p + 40]
            p += 1
        out.append((start, steps))
    return out


def lemmas(text):
    """the module's header and, per lemma, (comment, name, L, R, chains or None)"""
    first = re.search(r'^(-- .*\n)?lem-\S+ : ', text, re.M).start()
    header, body = text[:first], text[first:]
    starts = [m.start() for m in re.finditer(r'^(-- .*\n)?lem-\S+ : ', body, re.M)] + [len(body)]
    out = []
    for a, b in zip(starts, starts[1:]):
        blk = body[a:b]
        m = re.search(r'^(lem-\S+) : ⟪ (.*) ⟫ʷ ≈ ⟪ (.*) ⟫ʷ$', blk, re.M)
        name, L, R = m.group(1), m.group(2), m.group(3)
        comment = blk[:m.start()].rstrip('\n')
        dm = re.search(r'^' + re.escape(name) + r' = (.*)$', blk, re.M)
        out.append((comment, name, L, R, None if dm.group(1) == 'refl' else chains(blk)))
    return header, out


def steps_of(L, R, cs, name):
    """the lemma's steps as (kind, k, n, seg, ys, proof)"""
    cur = letters(L)
    out = []
    for start, ss in cs:
        assert start == cur, name
        for k, n, ys, proof in ss:
            seg = cur[k:k + n]
            cur = cur[:k] + ys + cur[k + n:]
            if proof == '(by-assoc Eq.refl)':
                out.append(('re', k, n, seg, ys, None))
            elif proof.startswith('(sym ') and proof.endswith(')'):
                out.append(('rw⁻', k, n, ys, seg, proof[5:-1]))
            else:
                out.append(('rw', k, n, seg, ys, proof))
    assert cur == letters(R), name
    return out


# the engine, Four/Reflect.agda
sys.argv = [sys.argv[0], REPO]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'reflect4_engine.py'), encoding='utf-8').read(), {'__name__': 'engine'})

mods = sorted(f[:-5] for f in os.listdir(D) if re.fullmatch(r'D\d+\.agda', f))
texts = {m: rd(os.path.join(D, m + '.agda')) for m in mods}
assert all('Four.Reflect' not in t for t in texts.values()), 'Four/D is already reflected'
parsed = {m: lemmas(texts[m]) for m in mods}

# ---------------------------------------------------------------- windows
spell = {}
for m in mods:
    for comment, name, L, R, cs in parsed[m][1]:
        if cs is None:
            continue
        for kind, k, n, a, b, proof in steps_of(L, R, cs, name):
            if proof and re.fullmatch(r'wn\d+', proof):
                assert spell.setdefault(proof, (tuple(a), tuple(b))) == (tuple(a), tuple(b)), proof
wins = sorted(spell)
src = {}
for f in sorted(os.listdir(os.path.join(T, 'Four/Wins'))):
    if re.fullmatch(r'W\d+\.agda', f):
        for n in re.findall(r'^(wn\d+) : ', rd(os.path.join(T, 'Four/Wins', f)), re.M):
            src[n] = 'W' + f[1:-5]
NW = max(int(w[2:]) for w in wins) + 1
entries = [None] * NW            # window n's name, or None (index 0, gaps)
for w in wins:
    entries[int(w[2:])] = w


def braun(ix):
    """the indices ix as a Braun tree: (root, left, right) or None"""
    if not ix:
        return None
    return (ix[0], braun(ix[1::2]), braun(ix[2::2]))


tree = braun(list(range(NW)))


def term(t, at, ind):
    """the tree t as nested constructor applications, `at i` the content of node i"""
    if t is None:
        return [ind + 'leaf']
    i, l, r = t
    return ([ind + '(node'] + term(l, at, ind + '  ') + [ind + '  ' + at(i)]
            + term(r, at, ind + '  ') + [ind + ')'])


def stmt(i):
    w = entries[i]
    return '[] []' if w is None else f'{lst(spell[w][0])} {lst(spell[w][1])}'


def prf(i):
    w = entries[i]
    return 'refl' if w is None else f'{src[w]}.{w}'


sig = ['''------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of the four-wire derivations, as a parameter
--
-- The derivations of Four.D take their windows as a module parameter, so
-- that they do not load completeness on three wires: each window is
-- stated over the macro letters (as Four.D uses it; every window has one
-- spelling there), the statements are a balanced tree (`windows`, the
-- n-th the statement of wnNNNNN for n = NNNNN), and a derivation takes
-- a tree of proofs (W : Ws), `wn n W` the n-th.  Records of the windows,
-- as Five.WinSig has, made a 6.4 MB interface that took 100 s and 7 GB
-- to check.  Four.WinInst builds the proofs from Four.Wins.  Written by
-- `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.WinSig where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)
open import Data.Unit.Base using (⊤ ; tt)

open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters

-- A Braun tree of statements: the n-th is at the root for n = 0, and
-- otherwise the ⌊(n − 1)/2⌋-th of the left subtree for n odd, of the
-- right one for n even.
data Tree : Set where
  leaf : Tree
  node : Tree → List Mac → List Mac → Tree → Tree

Win : Tree → ℕ → Set
Win leaf           _       = ⊤
Win (node a l r b) zero    = ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
Win (node a l r b) (suc n) = if n % 2 ≡ᵇ 0 then Win a (n / 2) else Win b (n / 2)

data Proofs : Tree → Set where
  leaf : Proofs leaf
  node : ∀ {a l r b} → Proofs a → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → Proofs b → Proofs (node a l r b)

private
  pick : (c : Bool) {A B : Set} → A → B → if c then A else B
  pick true  x y = x
  pick false x y = y

get : (t : Tree) → Proofs t → (n : ℕ) → Win t n
get leaf           leaf           n       = tt
get (node a l r b) (node pa p pb) zero    = p
get (node a l r b) (node pa p pb) (suc n) =
  pick (n % 2 ≡ᵇ 0) (get a pa (n / 2)) (get b pb (n / 2))

windows : Tree
windows =''']
sig += term(tree, stmt, '  ')
sig.append('''
Ws : Set
Ws = Proofs windows

wn : (n : ℕ) → Ws → Win windows n
wn n W = get windows W n''')
wr(os.path.join(T, 'Four/WinSig.agda'), '\n'.join(sig) + '\n')

inst = ['''------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of the four-wire derivations, the parameter of Four.D
--
-- Written by `scratchpad/four/reflect4.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.WinInst where

open import Examples.Groups.Clifford+CS.Four.Chain using (refl)
open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; leaf ; node)''']
inst += [f'import {P}Four.Wins.{w} as {w}' for w in sorted(set(src[x] for x in wins))]
inst += ['', 'ws : Ws', 'ws =']
inst += term(tree, prf, '  ')
wr(os.path.join(T, 'Four/WinInst.agda'), '\n'.join(inst) + '\n')

# ---------------------------------------------------------------- modules
DROP = re.compile(r'^open import ' + re.escape(P) + r'(TopWeakening|Idle|Completeness|Windows|Four\.Wins\.W\d+)( |$)')
nst = nre = neq = 0
for m in mods:
    header, lems = parsed[m]
    out_h = [f'{{-# OPTIONS --without-K --safe #-}}\n\nopen import {P}Four.WinSig using (Ws ; wn)\n']
    body = []
    table = {}
    for comment, name, L, R, cs in lems:
        if cs is None:
            body.append(('\n' + comment + '\n' if comment else '\n') + f'{name} : ⟪ {L} ⟫ʷ ≈ ⟪ {R} ⟫ʷ\n{name} = refl')
            continue
        steps, newq = [], []
        for kind, k, n, a, b, proof in steps_of(L, R, cs, name):
            nst += 1
            if kind == 're':
                steps.append(f're {k} {n} {lst(b)}')
                nre += 1
                continue
            proof = re.sub(r'(?<![\w-])wn(\d+)(?![\w-])', lambda mw: f'(wn {int(mw.group(1))} W)', proof)
            key = (tuple(a), tuple(b), proof)
            if key not in table:
                table[key] = f'q{len(table) + 1}'
                newq.append(key)
            steps.append(f'{kind} {k} {table[key]}')
        blk = []
        if newq:
            blk.append('\nprivate')
            for key in newq:
                blk.append(f'  {table[key]} : Eqn')
                blk.append(f'  {table[key]} = eqn {lst(list(key[0]))} {lst(list(key[1]))} {key[2]}')
        blk.append(('\n' + comment if comment else '') + f'\n{name} : ⟪ {L} ⟫ʷ ≈ ⟪ {R} ⟫ʷ')
        blk.append(f'{name} = derive {L} {R}')
        blk.append('  (' + ' ∷\n   '.join(steps) + ' ∷ []) Eq.refl')
        body.append('\n'.join(blk))
    neq += len(table)
    imps = []
    for line in header.split('\n'):
        if line.startswith('{-#') or not line.strip():
            continue
        if line.startswith('module '):
            imps.append(f'module {P}Four.D.{m} (W : Ws) where\n')
            continue
        if DROP.match(line):
            continue
        if line.startswith(f'open import {P}Four.Chain'):
            imps.append(f'open import {P}LowComm using (low-comm ; low₁-comm)')
            imps.append(f'open import {P}Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)')
            imps.append(f'open import {P}Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)')
            continue
        md = re.match(r'^open import (' + re.escape(P) + r'Four\.D\.D\d+) using ', line)
        if md:
            line = line.replace(md.group(1) + ' using ', md.group(1) + ' W using ', 1)
        imps.append(line)
    wr(os.path.join(D, m + '.agda'), '\n'.join(out_h + imps) + '\n' + '\n'.join(body) + '\n')

# ---------------------------------------------------------------- consumers
cons = []
for root, _, fs in os.walk(T):
    for f in fs:
        p = os.path.join(root, f)
        if not f.endswith('.agda') or os.path.dirname(p) == D:
            continue
        s = rd(p)
        if not re.search(r'^open import ' + re.escape(P) + r'Four\.D\.D\d+ using ', s, re.M):
            continue
        s = re.sub(r'^(open import ' + re.escape(P) + r'Four\.D\.D\d+) using ', r'\1 WI.ws using ', s, flags=re.M)
        s = re.sub(r'^(open import ' + re.escape(P) + r'Four\.D\.D\d+ WI\.ws using )',
                   f'import {P}Four.WinInst as WI\n' + r'\1', s, count=1, flags=re.M)
        wr(p, s)
        cons.append(os.path.relpath(p, T))
print(f'{len(mods)} modules, {nst} steps ({nre} re-bracketings), {neq} table equations, '
      f'{len(wins)} windows; consumers: {", ".join(sorted(cons))}')
