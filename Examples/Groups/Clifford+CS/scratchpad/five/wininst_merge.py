"""Five.WinInstL into Five.WinInst.

    python3 wininst_merge.py REPO

The literal windows' proofs (wsL, over the libraries WL01-09) and the
placed ones (ws, over WP01-08, which take the literal windows as an
argument) were two modules, the second importing the first: two links,
each loading its libraries' interfaces, at the end of a from-scratch run
(WinInstL then WinInst, 38 s and 24 s in one run, after the libraries).
This pass moves wsL into WinInst and deletes WinInstL.  Run it after
winlib5.py / wintree5.py / wsl_param.py / winbase.py; it does nothing if
WinInstL is gone already.
"""
import os, re, sys

REPO = sys.argv[1]
F = os.path.join(REPO, 'Examples/Groups/Clifford+CS/Five')
L, P, SIG = (os.path.join(F, n) for n in ('WinInstL.agda', 'WinInst.agda', 'WinSig.agda'))
NL = '\n'
if not os.path.exists(L):
    sys.exit(print('WinInstL already merged'))
ls = open(L, encoding='utf-8').read()
ps = open(P, encoding='utf-8').read()

IMP = re.compile(r'^(?:open import|import) .*$', re.M)
l_imps = IMP.findall(ls)
p_imps = IMP.findall(ps)
l_body = ls[ls.index('wsL : Complete 4 → WsL'):].rstrip(NL)
p_body = ps[ps.index('ws : Complete 4 → Ws'):].rstrip(NL)

def modname(line):
    return re.match(r'(?:open import|import) (\S+)', line).group(1)


# WinInst's own imports cover WinInstL's of the same modules (its WinSig
# list is a superset); WinInstL adds its libraries
imps, seen = [], set()
for line in p_imps + l_imps:
    m = modname(line)
    if m.endswith('Five.WinInstL') or m in seen:
        continue
    seen.add(m)
    imps.append(line)
# the libraries in order: WL before WP
wins = sorted([i for i in imps if '.Five.Wins.' in i], key=lambda i: i.split('.Wins.')[1])
rest = [i for i in imps if '.Five.Wins.' not in i]

head = ps[:ps.index('{-# OPTIONS')]
head = head.replace('-- The windows of the five-wire derivations, as a record',
                    '-- The windows of the five-wire derivations, as records')
head = head.replace('-- Written by `scratchpad/five/winlib5.py`.',
                    '-- The literal windows (wsL, over WL01-09) and the placed ones (ws,\n'
                    '-- over WP01-08, which take the literal ones as an argument).\n'
                    '-- Written by `scratchpad/five/winlib5.py`; wsL was Five.WinInstL\n'
                    '-- until `scratchpad/five/wininst_merge.py`.')
mod = re.search(r'^module \S+ where$', ps, re.M).group(0)
out = (head + '{-# OPTIONS --without-K --safe #-}' + NL + NL + mod + NL + NL
       + NL.join(rest + wins) + NL + NL + l_body + NL + NL + p_body + NL)
open(P, 'w', encoding='utf-8', newline=NL).write(out)
os.remove(L)

sig = open(SIG, encoding='utf-8').read()
new = sig.replace('Five.WinInstL and Five.WinInst build them.', 'Five.WinInst builds them.')
if new != sig:
    open(SIG, 'w', encoding='utf-8', newline=NL).write(new)
print('merged:', len(wins), 'libraries,', len(out), 'chars')
