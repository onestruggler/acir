#!/usr/bin/env python3
"""Dependency injection for the derivation modules of Four/D and Five/D.

    python3 di.py REPO Four|Five

A derivation module used to import the earlier ones whose lemmas it
rewrites with, so that the modules formed chains (Four/D 20 levels deep,
Five/D 18) and every module loaded the interfaces of everything below
it: loading was most of their checking time.  Here such a module takes
those lemmas as one parameter instead, `(Sᴰ : SDnnn)`, a list of proofs
typed by the lemmas' statements (DSig, DStmt), and names them in a
private block (`lem-x = at k S`), so that every derivation module
depends only on the shared infrastructure (the letters, the chain
engine, the window and lemma signatures) and all of them can be checked
at once.  `DAll` (Four.DAll W, Five.DAll) instantiates them in
dependency order -- each module's list, and one definition per lemma
that another module or a consumer uses -- and the consumers
(Four/Facts, Four/Bridge, ..., Five/F1, ...) import it instead.

What did not work, measured:
 * one parameter per lemma, typed by its statement: Agda abstracts every
   definition of a module over its whole telescope, and thirty statements
   of a few hundred letters made D527 take 58 s rather than 5;
 * one record per module: a record of up to 250 fields exhausted 8 GB
   (and the records of Four/D took 89 s), even with the fields typed by
   a statement's number;
 * the statements' tree beside the signatures: the positivity checker
   walks every definition of the module (26 s for 40 records).

The respelling modules R001-R011 of Five/D are derivation modules of
the same kind, over the literal windows (`c4 : WsL`, their lists
`All WsL ns`), and Five.Resps is one more consumer: they used to form a
chain five deep that Resps, the placed windows and every module of
Five/D waited for.  A module of Five/D takes a respelling lemma at `Ws`
(`lem-x c4` where it applied it to `lit c4`; the assembly passes
`λ c → lem-x (lit c)`).  The lemmas of Five.TR2 are taken the same way,
so that the modules using them need not wait for TR2 and the chain
F2 → Transport → TR2 below it; only Five.DAll.F1 imports TR2.

Idempotent: the pass reads a module's imports back off its private
block, so it can be rerun after a derivation module is regenerated
(with its imports).
"""
import os, re, sys, collections

REPO, TREE = sys.argv[1], sys.argv[2]
NL = '\n'
BASE = os.path.join(REPO, 'Examples/Groups/Clifford+CS')
DDIR = os.path.join(BASE, TREE, 'D')
PFX = 'Examples.Groups.Clifford+CS.'
MODP = PFX + TREE + '.D.'
FOUR = TREE == 'Four'
DSIG = PFX + TREE + '.DSig'
DSTMT = PFX + TREE + '.DStmt'
DEQN = PFX + TREE + '.DEqn'
DALL = PFX + TREE + '.DAll'
SIGF = os.path.join(BASE, TREE, 'DSig.agda')

CONSUMERS = {
    'Four': ['Four/Bridge.agda', 'Four/Facts/Bridges.agda', 'Four/Facts/Classes.agda',
             'Four/Facts/H1.agda', 'Four/Facts/HBridges.agda', 'Four/Facts/HClasses.agda',
             'Four/Facts/I2.agda', 'Four/Facts/I3.agda', 'Four/Facts/I4.agda',
             'Four/TransportTables.agda', 'Lemma87/Four.agda'],
    'Five': ['Five/F1.agda', 'Five/F1Low.agda', 'Five/F2.agda', 'Five/F4.agda', 'Five/F5.agda',
             'Five/Resps.agda'],
}[TREE]

# An import of a derivation module (D…, or a respelling module R…).
IMP = re.compile(r'^open import ' + re.escape(MODP) + r'([DR]\d+)(?: W)? using \(([^)]*)\)\n', re.M)
# Modules outside the tree whose lemmas are taken the same way.
EXT = {} if FOUR else {'TR2': PFX + 'Five.TR2'}
EXTIMP = {e: re.compile(r'^open import ' + re.escape(p) + r' using \(([^)]*)\)\n', re.M)
          for e, p in EXT.items()}
SIG = re.compile(r'^(lem-\S+) : (.*)$', re.M)
HDR = re.compile(r'^module ' + re.escape(MODP) + r'([DR]\d+)(.*?)where\n', re.M | re.S)
PRM = re.compile(r'^  \((lem-\S+) : (.*)\)$', re.M)
OPN = re.compile(r'^open SD\d+ S\n', re.M)
MARK = '-- The lemmas of other derivation modules (DSig).'
BLOCK = re.compile(r'^' + re.escape(MARK) + r'\nprivate\n((?:  .*\n)*)\n?', re.M)
STMT = re.compile(r'^(?:WsL? → )?⟪ (.*) ⟫ʷ ≈ ⟪ (.*) ⟫ʷ$')


def argof(m):
    # what a module's lemmas take: nothing (Four), the windows (Ws), or
    # the literal windows alone (WsL, the respelling modules)
    return '' if FOUR else ('WsL' if m.startswith('R') else 'Ws')

PRE = {
    'Four': ['open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)'],
    'Five': [],
}[TREE]


def names(s):
    return [x.strip() for x in s.split(';') if x.strip()]


# What earlier forms of the pass left in DSig: records of the lemmas.
old_rec = {}
if os.path.exists(SIGF):
    cur = None
    for line in open(SIGF, encoding='utf-8'):
        mm = re.match(r'^record S(D\d+) : Set where', line)
        if mm:
            cur = mm.group(1)
            old_rec[cur] = []
            continue
        mm = re.match(r'^    (lem-\S+) : ', line)
        if mm and cur:
            old_rec[cur].append(mm.group(1))

mods = sorted(f[:-5] for f in os.listdir(DDIR) if re.match(r'[DR]\d+\.agda$', f))
src, sig, owner, deps = {}, {}, {}, {}
for m in mods:
    s = open(os.path.join(DDIR, m + '.agda'), encoding='utf-8').read()
    src[m] = s
    for name, ty in SIG.findall(s):
        sig[name] = ty
        owner[name] = m
for e, p in EXT.items():
    s = open(os.path.join(REPO, *p.split('.')) + '.agda', encoding='utf-8').read()
    for name, ty in SIG.findall(s):
        sig[name] = ty
        owner[name] = e
for m in mods:
    s = src[m]
    used = collections.OrderedDict()
    for mod, ns in IMP.findall(s):
        for x in names(ns):
            used[x] = mod
    for e, rx in EXTIMP.items():
        for ns in rx.findall(s):
            for x in names(ns):
                used[x] = e
    h = HDR.search(s)
    for x, ty in PRM.findall(h.group(2)):
        used[x] = owner[x]
    if re.search(r'\(Sᴰ? : S[DR]\d+\)', h.group(2)):
        b = BLOCK.search(s)
        if b:
            for x in re.findall(r'^  (lem-\S+) : ', b.group(1), re.M):
                used[x] = owner[x]
        else:
            for x in old_rec[m]:
                used[x] = owner[x]
    deps[m] = used

# The statements the modules take, numbered.
taken = []
for m in mods:
    for x in deps[m]:
        if x not in taken:
            taken.append(x)
idx = {x: i for i, x in enumerate(taken)}


def render(m):
    s = src[m]
    used = deps[m]
    s = IMP.sub('', s)
    for rx in EXTIMP.values():
        s = rx.sub('', s)
    s = OPN.sub('', s)
    # a respelling lemma taken at Ws: applied to the windows, not lit c4
    if argof(m) == 'Ws':
        for x in used:
            if argof(owner[x]) == 'WsL':
                s = s.replace(f'({x} (lit c4))', f'({x} c4)')
    s = BLOCK.sub('', s)
    h = HDR.search(s)
    head = ('module ' + MODP + m + (' (W : Ws)' if FOUR else '') +
            (f' (Sᴰ : S{m})' if used else '') + ' where' + NL)
    s = s[:h.start()] + head + s[h.end():]
    if used:
        # the names, after the module's own imports
        body_start = s.index(head) + len(head)
        last = body_start
        for mm in re.finditer(r'^(?:open import|import) .*\n', s[body_start:], re.M):
            last = body_start + mm.end()
        block = [MARK, 'private']
        for k, x in enumerate(used):
            block.append(f'  {x} : ' + (argof(m) + ' → ' if argof(m) else '') + f'St {idx[x]}')
            block.append(f'  {x} = pickᴰ {k} Sᴰ')
        s = s[:last].rstrip(NL) + NL + NL + NL.join(block) + NL + NL + s[last:].lstrip(NL)
    # The table entries read off the trees: a window's, or an injected
    # lemma's, lists are its statement's (DEqn, DSig.sE), so that only
    # the entries for the module's own lemmas and the respelling ones
    # spell their lists.  Halved what a module costs besides loading.
    def entry(mm):
        head, prf = mm.group(1), mm.group(2)
        w = re.fullmatch(r'\(wn (\d+) W\)', prf)
        if w:
            return f'{head} wE {w.group(1)} W'
        w = re.fullmatch(r'\(wp (\d+) c4\)', prf)
        if w:
            return f'{head} wpE {w.group(1)} c4'
        w = re.fullmatch(r'\(wl (\d+) \(lit c4\)\)', prf)
        if w:
            return f'{head} wlE {w.group(1)} (lit c4)'
        w = re.fullmatch(r'\(wl (\d+) c4\)', prf)
        if w:
            return f'{head} wlE {w.group(1)} c4'
        w = re.fullmatch(r'\(?(lem-\S+?)( c4)?\)?', prf)
        if w and w.group(1) in used and bool(w.group(2)) == (not FOUR):
            x = w.group(1)
            return f'{head} sE {idx[x]} ' + (x if FOUR else f'({x} c4)')
        return mm.group(0)
    s = re.sub(r'^(  q\d+(?: c4)? =) eqn (?:\([^()]*\)|\[\]) (?:\([^()]*\)|\[\]) (.+)$', entry, s, flags=re.M)
    # an entry rewritten by an earlier run: its statement's number now
    s = re.sub(r'^(  q\d+(?: c4)? = sE )\d+ (\(?(lem-\S+?)(?: c4\))?)$',
               lambda mm: f'{mm.group(1)}{idx[mm.group(3)]} {mm.group(2)}', s, flags=re.M)
    pre_end = s.index('module ' + MODP + m)
    pre = s[:pre_end]
    lines = [l for l in pre.split(NL) if l.strip()]
    rest = [l for l in lines if not l.startswith('open import')]
    imps = list(PRE) + [f'open import {DEQN} using ({"wE" if FOUR else "wlE" if argof(m) == "WsL" else "wpE ; wlE"})'] + (
        [f'open import {DSTMT} using (St)', f'open import {DSIG} using (S{m} ; pickᴰ ; sE)'] if used else [])
    pre = NL.join(rest) + NL + NL + (NL.join(imps) + NL + NL if imps else '')
    return re.sub(r'\n{3,}', NL + NL, pre + s[pre_end:])


for m in mods:
    new = render(m)
    if new != src[m]:
        open(os.path.join(DDIR, m + '.agda'), 'w', encoding='utf-8').write(new)


def sides(x):
    mm = STMT.match(sig[x])
    return mm.group(1), mm.group(2)


TNODE, TLEAF = ('node', 'leaf') if FOUR else ('wnode', 'wleaf')


def tree(items):
    # the n-th at the root for n = 0, else in the left subtree for n odd
    if not items:
        return TLEAF
    left = [items[i] for i in range(1, len(items)) if i % 2 == 1]
    right = [items[i] for i in range(2, len(items)) if i % 2 == 0]
    l, r = items[0]
    return f'({TNODE} {tree(left)} {l} {r} {tree(right)})'


HEAD = ['{-# OPTIONS --without-K --safe #-}', '', '-' * 72, '-- Presentations of groups', '--']
TAIL = ['-' * 72, '']

out = HEAD + [
    '-- The statements of the lemmas the derivation modules of ' + TREE + '/D take',
    '--',
    "-- As a balanced tree (`lemmas`, `St n` the n-th), WinSig's.  In a",
    '-- module of its own: the positivity checker of a module walks every',
    '-- definition in it.  Written by `scratchpad/four/di.py`.'] + TAIL + [
    'module ' + DSTMT + ' where', '',
    'open import Data.List.Base using ([] ; _∷_)',
    'open import Data.Nat.Base using (ℕ)',
    ('open import Examples.Groups.Clifford+CS.Four.WinSig using (Tree ; leaf ; node ; Win)' if FOUR else
     'open import Examples.Groups.Clifford+CS.Five.WinSig using (WTree ; wleaf ; wnode ; WinT)'),
    'open import Examples.Groups.Clifford+CS.' + TREE + '.Letters', '',
    'lemmas : ' + ('Tree' if FOUR else 'WTree'),
    'lemmas = ' + tree([sides(x) for x in taken]), '',
    'St : ℕ → Set',
    'St n = ' + ('Win' if FOUR else 'WinT') + ' lemmas n']
open(os.path.join(BASE, TREE, 'DStmt.agda'), 'w', encoding='utf-8').write(NL.join(out) + NL)

out = HEAD + [
    '-- The lemmas each derivation module of ' + TREE + '/D takes',
    '--',
    '-- A module takes the lemmas of other derivation modules that it uses as',
    '-- one parameter, a list of proofs typed by their statements in DStmt',
    '-- (`All ns`, ns their numbers; `pickᴰ k` the k-th), and DAll builds the',
    '-- lists (scratchpad/four/di.py).  Records instead of lists were too',
    '-- slow to check: a record of 250 fields exhausted 8 GB.  Written by',
    '-- `scratchpad/four/di.py`.'] + TAIL + [
    'module ' + DSIG + ' where', '',
    'open import Data.List.Base using (List ; [] ; _∷_)',
    'open import Data.Nat.Base using (ℕ ; zero ; suc)',
    'open import Data.Unit.Base using (⊤ ; tt)']
if not FOUR:
    out.append('open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; WsL)')
out += ['open import ' + DSTMT + ' using (St ; lemmas)',
        'open import Examples.Groups.Clifford+CS.' + TREE + '.Reflect using (Eqn)',
        'open import ' + DEQN + ' using (getE)', '',
        '-- A lemma as an equation, its lists read off its statement.',
        'sE : (n : ℕ) → St n → Eqn',
        'sE n p = getE lemmas n p', '',
        'infixr 5 _∷ᵃ_']
if FOUR:
    out += ['data All : List ℕ → Set where',
            '  nil  : All []',
            '  _∷ᵃ_ : ∀ {n ns} → (St n) → All ns → All (n ∷ ns)', '',
            '-- The k-th statement of a list, and its proof.',
            'nth : List ℕ → ℕ → Set',
            'nth []       _       = ⊤',
            'nth (n ∷ ns) zero    = St n',
            'nth (n ∷ ns) (suc k) = nth ns k', '',
            'pickᴰ : ∀ {ns} (k : ℕ) → All ns → nth ns k']
else:
    out += ['-- A is what the lemmas take: the windows (Ws), or for the respelling',
            '-- modules the literal ones (WsL).',
            'data All (A : Set) : List ℕ → Set where',
            '  nil  : All A []',
            '  _∷ᵃ_ : ∀ {n ns} → (A → St n) → All A ns → All A (n ∷ ns)', '',
            '-- The k-th statement of a list, and its proof.',
            'nth : Set → List ℕ → ℕ → Set',
            'nth A []       _       = ⊤',
            'nth A (n ∷ ns) zero    = A → St n',
            'nth A (n ∷ ns) (suc k) = nth A ns k', '',
            'pickᴰ : ∀ {A ns} (k : ℕ) → All A ns → nth A ns k']
out += ['pickᴰ k       nil       = tt',
        'pickᴰ zero    (p ∷ᵃ ps) = p',
        'pickᴰ (suc k) (p ∷ᵃ ps) = pickᴰ k ps', '']
for m in mods:
    if deps[m]:
        out.append(f'S{m} : Set')
        out.append(f'S{m} = All ' + (argof(m) + ' ' if argof(m) else '') + '(' + ' ∷ '.join(str(idx[x]) for x in deps[m]) + ' ∷ [])')
open(SIGF, 'w', encoding='utf-8').write(NL.join(out) + NL)

TT, TL, TN, WIN = ('Tree', 'leaf', 'node', 'Win') if FOUR else ('WTree', 'wleaf', 'wnode', 'WinT')
out = HEAD + [
    '-- The windows of ' + TREE + '/D as equations',
    '--',
    "-- The n-th statement of a tree of statements (WinSig's) with its proof,",
    '-- as the equation the derivation engine rewrites with, its lists read',
    '-- off the tree alone (not off the proof, which is a variable where it',
    '-- is used): so a table entry of a derivation module need not spell',
    '-- the lists of its window or lemma, which was half of what a module',
    '-- cost besides loading.  Written by `scratchpad/four/di.py`.'] + TAIL + [
    'module ' + DEQN + ' where', '',
    'open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)',
    'open import Data.List.Base using ([] ; _∷_)',
    'open import Data.Nat.Base using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)', '',
    'open import Examples.Groups.Clifford+CS.' + TREE + '.Chain using (refl)',
    ('open import Examples.Groups.Clifford+CS.Four.WinSig using (Tree ; leaf ; node ; Win ; Ws ; windows ; wn)' if FOUR else
     'open import Examples.Groups.Clifford+CS.Five.WinSig\n  using (WTree ; wleaf ; wnode ; WinT ; Ws ; WsL ; windowsL ; windowsP ; wl ; wp)'),
    'open import Examples.Groups.Clifford+CS.' + TREE + '.Reflect using (Eqn ; eqn)', '',
    f'getE : (t : {TT}) (n : ℕ) → {WIN} t n → Eqn',
    f'getE {TL}           n       _ = eqn [] [] refl',
    f'getE ({TN} a l r b) zero    p = eqn l r p',
    f'getE ({TN} a l r b) (suc n) p = sel (n % 2 ≡ᵇ 0) p',
    '  where',
    f'  sel : (c : Bool) → (if c then {WIN} a (n / 2) else {WIN} b (n / 2)) → Eqn',
    '  sel true  q = getE a (n / 2) q',
    '  sel false q = getE b (n / 2) q', '']
if FOUR:
    out += ['wE : ℕ → Ws → Eqn', 'wE n W = getE windows n (wn n W)']
else:
    out += ['wpE : ℕ → Ws → Eqn', 'wpE n c4 = getE windowsP n (wp n c4)', '',
            'wlE : ℕ → WsL → Eqn', 'wlE n L = getE windowsL n (wl n L)']
open(os.path.join(BASE, TREE, 'DEqn.agda'), 'w', encoding='utf-8').write(NL.join(out) + NL)

# The consumers, and the assemblies they import: Four's one, DAll;
# Five's one per consumer (DAll.F1, ...), each the closure of what its
# consumer uses: some modules of Five/D take lemmas of Five.TR2, which
# reaches Five.F2 through Five.Transport, so that one assembly of
# everything would be a cycle.  The closure of what a consumer used is
# what it imported before, and that was not a cycle.
GROUPS = ([('DAll', CONSUMERS)] if FOUR else
          [('DAll.' + os.path.basename(c)[:-5], [c]) for c in CONSUMERS])
CIMP = re.compile(r'^open import ' + re.escape(MODP) + r'([DR]\d+)( WI\.ws| W)? using \(([^)]*)\)\n', re.M)
DIMP = re.compile(r'^open import ' + re.escape(DALL) + r'(?:\.\w+)?(?: WI\.ws)? using \(([^)]*)\)\n', re.M)


def visit_into(m, order, seen):
    if m in seen or m in EXT:
        return
    seen.add(m)
    for x, mod in deps[m].items():
        visit_into(mod, order, seen)
    order.append(m)


stale = os.path.join(BASE, TREE, 'DAll.agda')
total = 0
for gname, cons in GROUPS:
    gmod = PFX + TREE + '.' + gname
    cons_used = collections.OrderedDict()
    for c in cons:
        p = os.path.join(BASE, c)
        s = open(p, encoding='utf-8').read()
        ns = []
        for mod, arg, xs in CIMP.findall(s):
            ns += names(xs)
        for xs in DIMP.findall(s):
            ns += names(xs)
        for x in ns:
            cons_used[x] = owner[x]
        if ns:
            uniq = list(dict.fromkeys(ns))
            line = 'open import ' + gmod + (' WI.ws' if FOUR else '') + ' using (' + ' ; '.join(uniq) + ')' + NL
            state = {'first': True}

            def sub(mm):
                if state['first']:
                    state['first'] = False
                    return line
                return ''
            s2 = re.sub('(?:' + CIMP.pattern + ')|(?:' + DIMP.pattern + ')', sub, s, flags=re.M)
            if s2 != s:
                open(p, 'w', encoding='utf-8').write(s2)
    # the closure, in dependency order
    order, seen = [], set()
    for x in cons_used:
        visit_into(owner[x], order, seen)
    need = set(cons_used)
    for m in order:
        need |= set(deps[m])
    out = HEAD + [
        '-- The lemmas of ' + TREE + '/D ' + ('' if FOUR else 'that ' + os.path.basename(cons[0])[:-5] + ' uses, ') + 'instantiated',
        '--',
        '-- Each derivation module takes the lemmas of the others that it uses',
        '-- as a list (DSig); here every lemma that one uses, or that ' + ('a' if FOUR else 'the'),
        '-- consumer does, is the lemma of its module applied to its list, in',
        '-- dependency order.  Written by `scratchpad/four/di.py`.'] + TAIL
    if FOUR:
        out += ['open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws)', '',
                'module ' + gmod + ' (W : Ws) where']
    else:
        out.append('module ' + gmod + ' where')
    out += ['', 'open import ' + DSIG]
    lifted = any(argof(m) == 'Ws' and argof(owner[x]) == 'WsL' for m in order for x in deps[m])
    if lifted:
        out.append('open import Examples.Groups.Clifford+CS.Five.WinSig using (lit)')
    for e, p in EXT.items():
        xs = [x for x in sig if owner[x] == e and x in need]
        if xs:
            out.append(f'open import {p} using (' + ' ; '.join(xs) + ')')
    for m in order:
        out.append(f'import {MODP}{m} as {m}')
    out.append('')

    def item(m, x):
        if argof(m) == 'Ws' and argof(owner[x]) == 'WsL':
            return f'(λ c → {x} (lit c))'
        return x
    for m in order:
        args = (' W' if FOUR else '')
        if deps[m]:
            out.append(f's{m} : S{m}')
            out.append(f's{m} = ' + ' ∷ᵃ '.join(item(m, x) for x in deps[m]) + ' ∷ᵃ nil')
            args += f' s{m}'
        for x in [y for y in sig if owner[y] == m and y in need]:
            out.append(f'{x} : _')
            out.append(f'{x} = {m}.{x}{args}')
    path = os.path.join(BASE, TREE, *gname.split('.')) + '.agda'
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w', encoding='utf-8').write(NL.join(out) + NL)
    total += len(need)
    print(' ', gname, 'modules', len(order), 'lemmas', len(need), 'for the consumer', len(cons_used))
    if path == stale:
        stale = None
if stale and os.path.exists(stale):
    os.remove(stale)
print(TREE, 'modules', len(mods), 'taking lemmas', sum(1 for m in mods if deps[m]),
      'statements', len(taken), 'instantiated', total)
