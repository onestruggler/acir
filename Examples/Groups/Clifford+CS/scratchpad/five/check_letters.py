# Do derivn.unfold1 and spell5 regenerate Five/Letters.agda's box
# definitions?   python3 check_letters.py
import sys, os, itertools, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import prim5
from prim5 import norm1
import spell5 as S5
from spell5 import mname, box_def_name, letter_expr, paren
import derivn

ROOT = os.path.join(HERE, '..', '..', 'Five', 'Letters.agda')
text = open(ROOT, encoding='utf-8').read()
defs = dict(re.findall(r'^(b-\S+) = (.*)$', text, re.M))
W = range(5)
cand = []
for k in range(2, 5):
    for ws in itertools.permutations(W, k + 1):
        cand += [('BOX',) + ws, ('BOXd',) + ws]
for ws in itertools.permutations(W, 4):
    u, x, c, A = ws
    cand += [('SBOX', u, x, (c,), A), ('SBOXd', u, x, (c,), A)]
for ws in itertools.permutations(W, 5):
    u, x, c1, c2, A = ws
    cand += [('SBOX', u, x, (c1, c2), A), ('SBOXd', u, x, (c1, c2), A)]
byname = {box_def_name(g): g for g in cand}
ok = bad = 0
for name, rhs in defs.items():
    g = byname[name]
    us = [norm1(h) for h in derivn.unfold1(g)]
    mine = ' • '.join(paren(letter_expr(h)) for h in us)
    if mine == rhs: ok += 1
    else:
        bad += 1
        if bad <= 3: print('MISMATCH', name, '\n  file:', rhs[:200], '\n  mine:', mine[:200])
print(len(defs), 'box definitions,', ok, 'regenerated,', bad, 'differ')
