from chains import *
import pickle, sys
def lean_canon(w):
    out = []
    for x in reversed(w):
        # push x in front of out
        res = []; rest = out
        while rest and x in W0 and rest[0] in W1:
            res.append(rest[0]); rest = rest[1:]
        out = res + [x] + rest
    return ''.join(out)
def L(w): return '[' + ', '.join('.' + c for c in w) + ']'
def step(st):
    u, v, k, d = st
    return '⟨%s, %s, %d, %s⟩' % (L(u), L(v), k, 'true' if d else 'false')
BASEP = {'e1': 'ax_e1', 'e2': 'ax_e2', 'e3': 'ax_e3', 'e1u': 'ax_e1u', 'e2u': 'ax_e2u',
         'e3u': 'ax_e3u', 'e4': 'ax_e4', 'e5': 'ax_e5', 'e6': 'ax_e6', 'e7': 'ax_e7',
         'e9': 'ax_e9', 'e10': 'ax_e10', 'e11': 'ax_e11', 'f1': 'ax_f1', 'f2': 'ax_f2',
         'g': 'ax_g', 'def8': 'ax_def8'}
RAW = {n: (l, r) for n, l, r in BASE}
def export(lib, prefix, start_lib, start_index, label):
    """lines defining prefix_i for table entries start_index.. ; returns lines, last name"""
    lines = []
    prev = start_lib
    for i in range(start_index, len(lib.rules)):
        name, l, r = lib.rules[i]
        assert lean_canon(l) == l and lean_canon(r) == r, name
        _, _, p = lib.proofs[name]
        cur = '%s%d' % (prefix, i)
        e = '(%s, %s)' % (L(l), L(r))
        if p == 'axiom':
            rl, rr = RAW[name]
            pf = 'axc %s (by decide) (by decide)' % BASEP[name]
        elif isinstance(p, tuple):
            tag, src = p
            j = lib.idx(src)
            fn = {'r': 'byRev', 's': 'bySig', 'rs': 'byRevSig'}[tag]
            pf = '%s.%s %d _ (by decide +kernel)' % (prev, fn, j)
        else:
            pf = '%s.run _ _ [%s]\n    (by decide +kernel)' % (prev, ',\n      '.join(step(s) for s in p))
        lines.append('/-- %s %s -/' % (label, name))
        lines.append('def %s : Lib := %s.snoc %s\n  (%s)\n' % (cur, prev, e, pf))
        prev = cur
    return lines, prev
