# The canonical instance of ki-yb at n = 4 (Syntactics.hyb-yb): the
# decoded rule at (12, 13, 14, 15) with sink 11, at the top frame (the
# transport that makes k_14 the canonical hybrid).  Writes the Agda words
# (scratchpad/four/hyb_yb.agda-snippet) in the spelling of Four/Letters,
# each distinct middle word once, and registers the axiom's macro
# letters (AXIOMS['hyb-yb'], L['AXIOM HYB']).
import os, sys, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import fp, norm, show
from passes import L
import facts4 as F
from dec import Dec
from emit import mname, ROOT
from prim import AXIOMS

INST = (12, 13, 14, 15, 11)
KIND = {('pp', False): 'p', ('pp', True): "p'", ('rot', False): 'l', ('rot', True): 'h', ('ki', False): 'k'}

def sides():
    D = Dec(4)
    j, k, l, m, s = INST
    K = lambda a, b: D.ki(a, b, s)
    lhs = K(j, k) + K(l, m) + K(j, l) + K(k, m)
    rhs = K(j, l) + K(k, m) + K(j, k) + K(l, m)
    tolist = lambda keys: [(a, KIND[(kind, fl)]) for (kind, a, fl) in keys]
    return tolist(lhs), tolist(rhs)

def frame():
    import hybtop as HT
    return HT.frame_top()

def blocks(side, ops): return F.TF(ops, [F.decoded(a, kind) for a, kind in side])

def register():
    ops = frame()
    l, r = sides()
    Lb, Rb = blocks(l, ops), blocks(r, ops)
    lw, rw = norm(F.flat(Lb)), norm(F.flat(Rb))
    assert fp(lw) == fp(rw)
    AXIOMS['hyb-yb'] = (lw, rw)
    L['AXIOM HYB'] = (lw, rw)
    return Lb, Rb

def letters_table():
    tab = {}
    for line in open(os.path.join(ROOT, 'Letters.agda'), encoding='utf-8'):
        mm = re.match(r'^⟪ (\S+) ⟫ = (.*)$', line.rstrip('\n'))
        if mm: tab[mm.group(1)] = mm.group(2)
    return tab

def agda_words():
    Lb, Rb = register()
    tab = letters_table()
    mids = {}
    def mid_name(mid):
        mid = tuple(norm(list(mid)))
        if mid not in mids: mids[mid] = f'M{len(mids)}'
        return mids[mid]
    def block_expr(b):
        xs = ' • '.join(f'({tab[mname(("X", w))]})' for w in range(4) if b[0][w])
        mn = mid_name(b[1])
        return f'{xs} • {mn} • {xs}' if xs else mn
    lexprs = [block_expr(b) for b in Lb]; rexprs = [block_expr(b) for b in Rb]
    out = []
    names = ' '.join(mids.values())
    out.append(f'  {names} Yl Yr : Circuit (₄₊ n)')
    for mid, nm in mids.items():
        out.append(f'  {nm} = ' + ' • '.join(f'({tab[mname(g)]})' for g in mid))
    out.append('  Yl = ' + NL.join(['(' + e + ')' for e in lexprs]).replace(NL, '\n       • '))
    out.append('  Yr = ' + NL.join(['(' + e + ')' for e in rexprs]).replace(NL, '\n       • '))
    return '\n'.join(out) + '\n', len(mids)

def C_yb():
    """the decoded ki-yb at the canonical instance, at the top frame: the axiom."""
    from deriv import Derivation
    name = 'top ki-yb'
    if name in L: return name
    if 'AXIOM HYB' not in L: register()
    lw, rw = L['AXIOM HYB']
    d = Derivation(name, lw, rw, L)
    d.lemma('AXIOM HYB', 0)
    d.done(); return name

NL = '\n'
if __name__ == '__main__':
    text, nm = agda_words()
    open(os.path.join(os.path.dirname(HERE), 'hyb_yb.agda-snippet'), 'w', encoding='utf-8').write(text)
    print('mids', nm, 'chars', len(text))
