# Replace Five's window records by Braun trees, as Four.WinSig has:
#
#   python3 wintree5.py REPO [TREE]      (TREE Five, the default, or FiveV)
#
# Run on the record form of Five/WinSig (winlib5.py's), after reflect5.py.
# The literal windows (`wlNNNN`) and the placed ones (`wpNNNN`) become two
# trees of statements, `windowsL` and `windowsP`; `WsL` is a tree of proofs
# of the first, `Ws` a record of such a tree (`lit`) and a tree of proofs
# of the second; `wl n W`, `wp n W` are the n-th windows.  Five.WinInstL
# and Five.WinInst build the trees, and the derivations of Five/D refer to
# `(wl n (lit c4))`, `(wp n c4)`.  Records of the windows made a 5.2 MB
# interface that took 97 s and 2.4 GB to check.
import os, re, sys

REPO = sys.argv[1]
TREE = sys.argv[2] if len(sys.argv) > 2 else 'Five'
F = os.path.join(REPO, 'Examples/Groups/Clifford+CS', TREE)
P = 'Examples.Groups.Clifford+CS.'


def rd(p):
    return open(p, encoding='utf-8').read()


def wr(p, s):
    open(p, 'w', encoding='utf-8', newline='\n').write(s)


sig = rd(os.path.join(F, 'WinSig.agda'))
assert 'record WsL01' in sig, 'Five/WinSig is not in record form'
stmt = {'l': {}, 'p': {}}
for kind, n, st in re.findall(r'^    w([lp])(\d+) : (⟪ .* ⟫ʷ ≈ ⟪ .* ⟫ʷ)$', sig, re.M):
    stmt[kind][int(n)] = st
src = {'l': {}, 'p': {}}
for f in sorted(os.listdir(os.path.join(F, 'Wins'))):
    m = re.fullmatch(r'W([LP])(\d+)\.agda', f)
    if m:
        for kind, n in re.findall(r'^w([lp])(\d+) : ', rd(os.path.join(F, 'Wins', f)), re.M):
            src[kind][int(n)] = f[:-5]
assert set(stmt['l']) == set(src['l']) and set(stmt['p']) == set(src['p'])


def braun(ix):
    if not ix:
        return None
    return (ix[0], braun(ix[1::2]), braun(ix[2::2]))


def term(t, at, ind, leaf, node):
    if t is None:
        return [ind + leaf]
    i, l, r = t
    return ([ind + '(' + node] + term(l, at, ind + '  ', leaf, node) + [ind + '  ' + at(i)]
            + term(r, at, ind + '  ', leaf, node) + [ind + ')'])


trees = {k: braun(list(range(max(stmt[k]) + 1))) for k in 'lp'}


def st_at(k):
    def at(i):
        s = stmt[k].get(i)
        if s is None:
            return '[] []'
        m = re.fullmatch(r'⟪ (.*) ⟫ʷ ≈ ⟪ (.*) ⟫ʷ', s)
        return f'{m.group(1)} {m.group(2)}'
    return at


def pf_at(k):
    def at(i):
        return f'({src[k][i]}.w{k}{i:04} c4)' if i in src[k] else 'refl'
    return at


head = sig[:sig.index('{-# OPTIONS')]
head = re.sub(r'-- The windows of the five-wire derivations, as records\n(--.*\n)*?-{20,}\n',
              '''-- The windows of the five-wire derivations, as trees
--
-- The derivations of Five.D take their windows as an argument (see
-- `scratchpad/five/winlib5.py`): `WsL` proves the literal windows and
-- the two-wire equations of Five.D.TR, `Ws` holds those (`lit`) and the
-- placed windows.  The statements are two Braun trees, `windowsL` and
-- `windowsP`, the n-th the statement of wlNNNN, resp. wpNNNN, for
-- n = NNNN, and `wl n W`, `wp n W` the n-th proofs; records of the
-- windows, as this module had, made a 5.2 MB interface that took 97 s
-- and 2.4 GB to check.  Five.WinInstL and Five.WinInst build them.
-- Written by `scratchpad/five/wintree5.py`.
------------------------------------------------------------------------
''', head)
if TREE != 'Five':
    head = head.replace('Five.D', TREE + '.D').replace('Five.WinInst', TREE + '.WinInst')
out = [head +'''{-# OPTIONS --without-K --safe #-}


module Examples.Groups.Clifford+CS.''' + TREE + '''.WinSig where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)
open import Data.Unit using (⊤ ; tt)

open import Examples.Groups.Clifford+CS.''' + TREE + '''.Chain using (Mac ; ⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.''' + TREE + '''.Letters

-- A Braun tree of statements: the n-th is at the root for n = 0, and
-- otherwise the ⌊(n − 1)/2⌋-th of the left subtree for n odd, of the
-- right one for n even.
data WTree : Set where
  wleaf : WTree
  wnode : WTree → List Mac → List Mac → WTree → WTree

WinT : WTree → ℕ → Set
WinT wleaf           _       = ⊤
WinT (wnode a l r b) zero    = ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
WinT (wnode a l r b) (suc n) = if n % 2 ≡ᵇ 0 then WinT a (n / 2) else WinT b (n / 2)

data WProofs : WTree → Set where
  pleaf : WProofs wleaf
  pnode : ∀ {a l r b} → WProofs a → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → WProofs b → WProofs (wnode a l r b)

private
  pick : (c : Bool) {A B : Set} → A → B → if c then A else B
  pick true  x y = x
  pick false x y = y

wget : (t : WTree) → WProofs t → (n : ℕ) → WinT t n
wget wleaf           pleaf           n       = tt
wget (wnode a l r b) (pnode pa p pb) zero    = p
wget (wnode a l r b) (pnode pa p pb) (suc n) =
  pick (n % 2 ≡ᵇ 0) (wget a pa (n / 2)) (wget b pb (n / 2))

windowsL : WTree
windowsL =''']
out += term(trees['l'], st_at('l'), '  ', 'wleaf', 'wnode')
out.append('\nwindowsP : WTree\nwindowsP =')
out += term(trees['p'], st_at('p'), '  ', 'wleaf', 'wnode')
out.append('''
WsL : Set
WsL = WProofs windowsL

record Ws : Set where
  no-eta-equality
  field
    lit : WsL
    pl  : WProofs windowsP

open Ws public using (lit)

-- The n-th literal and placed windows.
wl : (n : ℕ) → WsL → WinT windowsL n
wl n W = wget windowsL W n

wp : (n : ℕ) → Ws → WinT windowsP n
wp n W = wget windowsP (Ws.pl W) n''')
wr(os.path.join(F, 'WinSig.agda'), '\n'.join(out) + '\n')

for name, k, ty, extra in [('WinInstL', 'l', 'WsL', ''), ('WinInst', 'p', 'Ws', '')]:
    p = os.path.join(F, name + '.agda')
    s = rd(p)
    i = s.index('\n' + ('wsL01' if k == 'l' else 'ws01') + ' : ')
    pre = s[:i]
    pre = re.sub(r'open import ' + re.escape(P) + TREE + r'\.WinSig using \([^)]*\)',
                 f'open import {P}{TREE}.WinSig using ({"WsL" if k == "l" else "Ws ; WsL"} ; pleaf ; pnode)', pre)
    pre = pre.replace('open import ' + P + 'Completeness using (Complete)\n',
                      'open import ' + P + 'Completeness using (Complete)\n'
                      'open import ' + P + TREE + '.Chain using (refl)\n')
    body = []
    if k == 'l':
        body += ['', 'wsL : Complete 4 → WsL', 'wsL c4 =']
        body += term(trees['l'], pf_at('l'), '  ', 'pleaf', 'pnode')
    else:
        body += ['', 'ws : Complete 4 → Ws', 'ws c4 = record', '  { lit = wsL c4', '  ; pl  =']
        body += term(trees['p'], pf_at('p'), '      ', 'pleaf', 'pnode')
        body.append('  }')
    wr(p, pre.rstrip('\n') + '\n' + '\n'.join(body) + '\n')

nd = 0
for f in sorted(os.listdir(os.path.join(F, 'D'))):
    if not re.fullmatch(r'[A-Z]\d+\.agda', f):
        continue
    p = os.path.join(F, 'D', f)
    s = rd(p)
    s = re.sub(r'^(open import ' + re.escape(P) + TREE + r'\.WinSig) using \(([^)]*)\)',
               lambda m: m.group(1) + ' using (' + ' ; '.join(
                   [x for x in ('Ws', 'WsL', 'lit') if re.search(r'(?<![\w-])' + x + r'(?![\w-])', m.group(2))]
                   + ['wl', 'wp']) + ')', s, flags=re.M)
    s = re.sub(r'(?<![\w-])w([lp])(\d{4})(?![\w-])', lambda m: f'w{m.group(1)} {int(m.group(2))}', s)
    wr(p, s)
    nd += 1
print(f"{len(stmt['l'])} literal and {len(stmt['p'])} placed windows; {nd} modules of {TREE}/D")
