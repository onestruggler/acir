"""Decision trees for Clement's Case 3.4, with normalisation and shared subtrees
(the trees of Tree.agda, over the forms and checks of core.py).

Nodes (rows are names; Agda order is the list order):
  ('split', v, us, t0, t1)
  ('leaf', cand)
  ('extend', delta, kappa, route, cert, minpairs, row, var, sub)
  ('conj', g, sub)                       letter g on the window, apart from the pair or Z on its second index
  ('relabel', newrows, sw, sub)           newrows: (role, old row) in the new order; sw: the pair reversed
  ('reparam', nf, tau, sub)               tau: NF var -> form in the old vars; the sub uses the NF's vars
  ('use', nf)
"""
import itertools, sys
from collections import Counter
from core import *

CORE20 = [('H',0,2),('H',1,3),('H',0,1),('Z',0),('Z',1),('H',1,3),('H',0,2),('H',0,1),('H',0,2),('H',1,3),('Z',1),('Z',0),('H',0,1),('H',1,3),('H',0,2)]
CORE30 = [('H',0,2),('H',1,3),('H',0,4),('H',1,5),('H',0,1),('Z',0),('Z',1),('H',1,5),('H',0,4),('H',1,3),('H',0,2),('H',0,1),
          ('H',0,2),('H',1,3),('H',0,4),('H',1,5),('Z',1),('Z',0),('H',0,1),('H',1,5),('H',0,4),('H',1,3),('H',0,2)]

class Node:
    def __init__(s, rows, fs, vars, tags, mini, ic, id_):
        s.rows, s.fs, s.vars, s.tags, s.mini, s.ic, s.id = rows, fs, vars, tags, mini, ic, id_
    def subst(s, env):
        return Node(s.rows, {r: f.subst(env) for r, f in s.fs.items()}, s.vars, s.tags, s.mini, s.ic, s.id)
    def with_fs(s, fs): return Node(s.rows, fs, s.vars, s.tags, s.mini, s.ic, s.id)

def relabel_route(core, lab):
    return [('Z', lab[g[1]]) if g[0] == 'Z' else (g[0], lab[g[1]], lab[g[2]]) for g in core]

def undo(a, b, l): return ('X', a, b) if l == b else ('Z', l)

def cand_route(cand):
    core = CORE20 if cand['core'] == '20' else CORE30
    lab = cand['lab']; a, b = lab[0], lab[1]
    closing = []
    for l in cand['Q']: closing = [undo(a, b, l)] + closing
    r = [('Z', l) for l in cand['Q']] + relabel_route(core, lab) + closing
    if cand['flip']: r = r + [('Z', b), ('X', a, b)]
    return r

STATS = Counter()

def split(node, d, cont):
    us = list(d.us); v = us[-1]
    out = []
    for b in (0, 1):
        h = const(b) + var(v, R2)
        for u in us[:-1]: h = h - var(u)
        out.append(cont(node.subst({v: h})))
    STATS['split'] += 1
    return ('split', v, tuple(us), out[0], out[1])

def drive(node, f, depth=0):
    if depth > 30: raise RuntimeError('too deep')
    try:
        return f(node)
    except Dep as d:
        return split(node, d, lambda nd: drive(nd, f, depth + 1))

HOT = []
def ckey(c): return (c['core'], c['lab'], tuple(c['Q']), c['flip'])
def leaf_search(node, cands):
    deps = {}
    keys = {ckey(c): c for c in cands}
    order = [keys[k] for k in HOT if k in keys] + cands
    for cand in order:
        try:
            if check(cand_route(cand), node.fs):
                STATS['leaf'] += 1
                k = ckey(cand)
                if k in HOT: HOT.remove(k)
                HOT.insert(0, k)
                return ('leaf', cand)
        except Dep as d:
            key = (d.kind, d.us)
            deps[key] = max(deps.get(key, 0), d.pos)
    if not deps: return None
    (kind, us) = max(deps, key=lambda k: (deps[k], -len(k[1])))
    raise Dep(kind, us)

def powsq(delta):
    co = ONE
    for _ in range(delta): co = zmul(co, R2)
    return co

# --- counting (extensions) ---
def local_forms(node, route, delta):
    fs = run(route, node.fs)
    assert fs is not None, 'count route fails'
    out = {}
    for r in node.rows:
        f = fs[r]
        for _ in range(delta):
            f = f.half()
            assert f is not None, ('not divisible', r, delta)
        out[r] = f
    return out

def parities(gs, rows):
    par = {}
    for r in rows:
        f = gs[r]
        if oddF(f): par[r] = 1
        elif evenF(f): par[r] = 0
        else: raise Dep('par', par_dep(f))
    return par

def odd_sum(gs, rows, par):
    t = F()
    for r in rows:
        if par[r]: t = t + gs[r]
    return t

def find_cert(gs, rows):
    pairs = []; dep = None
    for a, b in itertools.combinations(rows, 2):
        s = gs[a] + gs[b]
        if oddF(s): pairs.append((a, b))
        elif not evenF(s) and dep is None: dep = par_dep(s)
    for p in pairs:
        for q in pairs:
            if len({p[0], p[1], q[0], q[1]}) == 4: return p + q
    if dep: raise Dep('par', dep)
    raise RuntimeError('no certificate')

def depth_quot(node, r, delta):
    f = node.fs[r]
    for _ in range(delta): f = f.half()
    return f

def find_minpairs(node, delta):
    out = []
    for dd in range(1, delta):
        rs = [r for r in node.rows if node.tags.get(r) == dd]
        found = None
        for a, b in itertools.combinations(rs, 2):
            s = depth_quot(node, a, dd) + depth_quot(node, b, dd)
            if clsF(s) == 1: found = (a, b); break
        assert found, ('minimality pair', dd)
        out.append(found)
    return out

def extend(node, delta, kappa, route, row, cont):
    assert node.mini
    gs = local_forms(node, route, delta)
    rows = node.rows
    cert = find_cert(gs, rows)
    if kappa is None:
        tot = F()
        for r in rows: tot = tot + gs[r]
        if not oddF(tot):
            if evenF(tot): raise RuntimeError('local count even')
            raise Dep('par', par_dep(tot))
    else:
        par = parities(gs, rows)
        os_ = odd_sum(gs, rows, par)
        c1 = clsF(os_)
        if c1 is None: raise Dep('cls', cls_dep(os_))
        n = sum(par.values())
        if kappa == 1: assert c1 == 1, ('class-1 count even', par)
        else: assert (n + c1) % 2 == 1, ('class-0 count even', par)
    minpairs = find_minpairs(node, delta)
    v = 'v' + row
    w = const(1) + var(v, R2) if kappa is None else const(1, kappa) + var(v, (2, 0))
    fs = dict(node.fs); fs[row] = w.scale(powsq(delta))
    tags = dict(node.tags); tags[row] = delta
    n2 = Node([row] + node.rows, fs, [v] + node.vars, tags, True, node.ic, node.id)
    STATS['extend'] += 1
    return ('extend', delta, kappa, tuple(route), cert, tuple(minpairs), row, v, cont(n2))

# --- conjugation ---
def conj_ok(node, g):
    """the edge g out of s and the edge out of H_cd s that it needs (raises Dep)"""
    a, b = node.ic, node.id
    idx = [g[1]] if g[0] == 'Z' else [g[1], g[2]]
    special = (g == ('Z', b))
    if not special and (a in idx or b in idx): return False
    fs1 = stepF(g, node.fs)
    if fs1 is None or kindF(fs1) != 'atL': return False
    if not check([g], node.fs): return False
    fcd = stepF(('H', a, b), node.fs)
    if fcd is None: return False
    g2 = ('X', a, b) if special else g
    if not check([g2], fcd): return False
    return True

def conj(node, g, cont):
    assert conj_ok(node, g), g
    fs1 = stepF(g, node.fs)
    tags = dict(node.tags); mini = node.mini
    if g[0] == 'X':
        tags = {(g[2] if r == g[1] else g[1] if r == g[2] else r): t for r, t in tags.items()}
    if g[0] == 'H':
        tags.pop(g[1], None); tags.pop(g[2], None); mini = False
    n2 = Node(node.rows, fs1, node.vars, tags, mini, node.ic, node.id)
    STATS['conj'] += 1
    return ('conj', g, cont(n2))

# --- normal forms ---
class NF:
    def __init__(s, name, roles, vars, fs, pivots, tags):
        s.name, s.roles, s.vars, s.fs, s.pivots, s.tags = name, roles, vars, fs, pivots, tags

def mk_nf38():
    a2, a3, a4, a5, b3, b4, b5, c3, c4, c5, d4, d5, e3, f3 = [var(x) for x in 'a2 a3 a4 a5 b3 b4 b5 c3 c4 c5 d4 d5 e3 f3'.split()]
    two = (2, 0); tr2 = (0, 2); four = (4, 0); fr2 = (0, 4); r2 = (0, 1)
    def lin(*ts):
        f = F()
        for co, t in ts: f = f + t.scale(co)
        return f
    c = const(1, 1) + lin((two, a2), (tr2, a3), (four, a4), (fr2, a5))
    d = const(1) + lin(((-2, 0), a2), (tr2, b3), (four, b4), (fr2, b5))
    e = const(1, 1) + lin((two, a2), (tr2, c3), (four, c4), (fr2, c5))
    f = const(1) + lin(((-2, 0), a2), ((0, -2), a3), ((0, -2), b3), ((0, -2), c3), (four, d4), (fr2, d5))
    x = (const(1) + lin(((0, -1), const(1) + a3 + c3), ((-2, 0), a2 + a4 + c4), (tr2, e3))).scale(r2)
    y = (const(1) + lin((r2, a3 + c3), (two, a2 - b4 - d4), (tr2, f3))).scale(r2)
    fs = {'y': y, 'x': x, 'c': c, 'd': d, 'e': e, 'f': f}
    pivots = [('c', 'a2', ['a3', 'a4', 'a5']), ('d', 'b3', ['b4', 'b5']), ('e', 'c3', ['c4', 'c5']),
              ('f', 'd4', ['d5']), ('x', 'e3', []), ('y', 'f3', [])]
    return NF('nf38', ['y', 'x', 'c', 'd', 'e', 'f'], 'a2 a3 a4 a5 b3 b4 b5 c3 c4 c5 d4 d5 e3 f3'.split(), fs, pivots, {'x': 1, 'y': 1})

def mk_nf341():
    a2, a3, a4, a5, b3, b4, b5, c3, c4, c5, d4, d5 = [var(x) for x in 'a2 a3 a4 a5 b3 b4 b5 c3 c4 c5 d4 d5'.split()]
    two = (2, 0); tr2 = (0, 2); four = (4, 0); fr2 = (0, 4)
    def lin(*ts):
        f = F()
        for co, t in ts: f = f + t.scale(co)
        return f
    c = const(1, 1) + lin((two, a2), (tr2, a3), (four, a4), (fr2, a5))
    d = const(1) + lin((two, a2), (tr2, b3), (four, b4), (fr2, b5))
    e = const(1, 1) + lin((two, a2), (tr2, c3), (four, c4), (fr2, c5))
    f = const(1) + lin((two, a2), (tr2, const(1) + a3 + b3 + c3), (four, d4), (fr2, d5))
    fs = {'c': c, 'd': d, 'e': e, 'f': f}
    pivots = [('c', 'a2', ['a3', 'a4', 'a5']), ('d', 'b3', ['b4', 'b5']), ('e', 'c3', ['c4', 'c5']), ('f', 'd4', ['d5'])]
    return NF('nf341', ['c', 'd', 'e', 'f'], 'a2 a3 a4 a5 b3 b4 b5 c3 c4 c5 d4 d5'.split(), fs, pivots, {})

NF38 = mk_nf38(); NF341 = mk_nf341()

class Impossible(Exception): pass

def divide(R, co):
    """R / co for co = +-sqrt2^k (raises Dep / Impossible)"""
    sign = 1
    if co[0] < 0 or (co[0] == 0 and co[1] < 0): sign = -1; co = zneg(co)
    k = 0; c = co
    while c != ONE:
        assert c[0] % 2 == 0, co
        c = (c[1], c[0] // 2); k += 1
    for _ in range(k):
        h = R.half()
        if h is None:
            us = par_dep(R)
            if us: raise Dep('par', us)
            raise Impossible()
        R = h
    return R if sign == 1 else -R

def reparam_solve(fs, nf):
    tau = {}
    for role, pv, zeros in nf.pivots:
        for z in zeros: tau[z] = F()
        row = nf.fs[role]
        rest = F(row.c, {k: x for k, x in row.v.items() if k != pv})
        for k in rest.v: assert k in tau, (role, k)
        R = fs[role] - rest.subst(tau)
        tau[pv] = divide(R, row.v[pv])
    for v in nf.vars: tau.setdefault(v, F())
    for role in nf.roles:
        assert nf.fs[role].subst(tau).key() == fs[role].key(), role
    return tau

def normalize(node, nf):
    """relabel (swap of the pair), signs, reparametrisation into nf (raises Dep)"""
    deps = Counter(); tried = 0
    for sw in (False, True):
        if sw:
            sub = {'c': 'd', 'd': 'c', 'e': 'f', 'f': 'e', 'x': 'y', 'y': 'x'}
        else:
            sub = {r: r for r in 'cdefxy'}
        newrows = [(role, sub[role]) for role in nf.roles]
        fs_r = {role: node.fs[old] for role, old in newrows}
        signable = [r for r in nf.roles if r != 'c']
        for k in range(len(signable) + 1):
            for sg in itertools.combinations(signable, k):
                fs2 = dict(fs_r)
                for r in sg: fs2[r] = -fs2[r]
                tried += 1
                try:
                    tau = reparam_solve(fs2, nf)
                except Dep as d:
                    deps[(d.kind, d.us)] += 1; continue
                except Impossible:
                    continue
                return build_norm(node, nf, newrows, sw, sg, tau)
    if not deps: raise RuntimeError('normalisation impossible')
    (kind, us), _ = deps.most_common(1)[0]
    raise Dep(kind, us)

def build_norm(node, nf, newrows, sw, sg, tau):
    STATS['norm'] += 1
    if sw:
        # Hs c d = Xs d c • Z c • Hs d c: the letters Z c, X d c out of Hs d c · s
        fsw = stepF(('H', node.id, node.ic), node.fs)
        assert fsw is not None and check([('Z', node.ic), ('X', node.id, node.ic)], fsw), 'flip'
    fs_r = {role: node.fs[old] for role, old in newrows}
    tags = {role: node.tags[old] for role, old in newrows if old in node.tags}
    n1 = Node([r for r, _ in newrows], fs_r, node.vars, tags, node.mini, 'c', 'd')
    def after_signs(n, sg):
        if not sg:
            return ('reparam', nf.name, tau, ('use', nf.name))
        return conj(n, ('Z', sg[0]), lambda n2: after_signs(n2, sg[1:]))
    return ('relabel', tuple(newrows), sw, after_signs(n1, list(sg)))

# --- the top: normalisation and the extras ---
SIG = [('H', 'c', 'e'), ('H', 'd', 'f')]

def odd_classes(node, route, delta):
    gs = local_forms(node, route, delta)
    par = parities(gs, node.rows)
    cl = {}
    for r in node.rows:
        if par[r]:
            c = clsF(gs[r])
            if c is None: raise Dep('cls', cls_dep(gs[r]))
            cl[r] = c
    return cl

def top(node):
    cl = odd_classes(node, SIG, 1)
    oc = [r for r in 'ce' if r in cl]; od = [r for r in 'df' if r in cl]
    assert len(oc) == 1 and len(od) == 1
    k0, k1 = cl[oc[0]], cl[od[0]]
    if k0 == k1:
        return normalize(node, NF341)
    return extend(node, 1, k0, SIG, 'x', lambda n1: extend(n1, 1, k1, SIG, 'y', lambda n2: drive(n2, lambda nd: normalize(nd, NF38))))

def root():
    fs = {'c': const(1) + var('v0', R2),
          'd': const(1, 1) + var('v0', R2) + var('v1', (2, 0)),
          'e': const(1) + var('v0', R2) + var('v2', (2, 0)),
          'f': const(1, 1) + var('v0', R2) + var('v1', (2, 0)) + var('v3', (2, 0))}
    return Node(['c', 'd', 'e', 'f'], fs, ['v0', 'v1', 'v2', 'v3'], {}, True, 'c', 'd')

# --- the normal-form subtrees ---
def labs4(): return [(('c','d','e','f'), False), (('d','c','f','e'), True)]

def fam20(node):
    for lab, flip in labs4():
        for qs in itertools.product((0, 1), repeat=3):
            yield dict(core='20', lab=lab, Q=[lab[i + 1] for i in range(3) if qs[i]], flip=flip)

def fam30(node, pool=('x', 'y')):
    for lab4, flip in labs4():
        for xy in itertools.permutations(pool, 2):
            lab = lab4 + xy
            for qs in itertools.product((0, 1), repeat=5):
                yield dict(core='30', lab=lab, Q=[lab[i + 1] for i in range(5) if qs[i]], flip=flip)

def nf_node(nf):
    return Node(list(nf.roles), dict(nf.fs), list(nf.vars), dict(nf.tags), True, 'c', 'd')

def nf341_tree(node):
    t = leaf_search(node, list(fam20(node)))
    if t is None: raise RuntimeError('3.4.1 fails')
    return t

def nf38_tree(node):
    t = leaf_search(node, list(fam30(node)))
    if t is None:
        STATS['stuck'] += 1
        return drive(node, stage3)
    return t

def stage3(node):
    gs = local_forms(node, SIG, 1)
    par = parities(gs, node.rows)
    oc = [r for r in 'ce' if par[r]][0]; od = [r for r in 'df' if par[r]][0]
    sig2 = SIG + [('H', oc, 'x'), ('H', od, 'y')]
    def after_jl(n3):
        g3 = local_forms(n3, sig2, 2)
        p3 = parities(g3, n3.rows)
        cl = {}
        for r in n3.rows:
            if p3[r]:
                c = clsF(g3[r])
                if c is None: raise Dep('cls', cls_dep(g3[r]))
                cl[r] = c
        pairs = []
        for b in (0, 1):
            rs = [r for r in n3.rows if cl.get(r) == b]
            assert len(rs) % 2 == 0
            for i in range(0, len(rs), 2): pairs.append(('H', rs[i], rs[i + 1]))
        return extend(n3, 3, None, sig2 + pairs, 'm', lambda n4: drive(n4, stage4))
    return extend(node, 2, 0, sig2, 'j', lambda n1: extend(n1, 2, 1, sig2, 'l', lambda n2: drive(n2, after_jl)))

def stage4(node):
    for p in ('j', 'l'):
        g = ('H', p, 'm')
        if not conj_ok(node, g): continue
        fs1 = stepF(g, node.fs)
        n1 = Node(node.rows, fs1, node.vars, {}, False, node.ic, node.id)
        t = leaf_search(n1, list(fam30(n1, pool=('x', 'y', p, 'm'))))
        if t is not None:
            STATS['conj'] += 1
            return ('conj', g, t)
    raise RuntimeError('stage 4 fails')

def size(t):
    k = t[0]
    if k in ('leaf', 'use'): return 1
    if k == 'split': return size(t[3]) + size(t[4])
    return size(t[-1])

def build():
    """the three trees: from the root forms (top) and of the two normal forms"""
    sys.setrecursionlimit(20000)
    t341 = drive(nf_node(NF341), nf341_tree)
    t38 = drive(nf_node(NF38), nf38_tree)
    t0 = drive(root(), top)
    return {'top': t0, 'nf38': t38, 'nf341': t341}
