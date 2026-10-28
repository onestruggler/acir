"""Derivations of the supplement's lemmas L1-L19 and of the typed relations
(Appendix B of the paper) from the reduced relations R1-R16 (Figure 1),
following the supplement's own derivations line by line.

Each line of a supplement derivation is read off its drawing
(`suppdraw.py`) and expanded into letters (`paper.expand`).  Each step is
then one rewrite by an equation its label names, found by
`engine.try_step` up to commuting letters; a 'Def' step is a rearrangement
(the derived generators are expanded by their definitions); an unlabelled
or unknown label may use any equation derived so far.  Where a drawn line
does not denote the same operator as its neighbours (a slip of the
supplement), the line is skipped and the two steps around it are done
together.
"""
import engine
import paper
from engine import Deriv, canon, reorder_to, solve_inv, strip_w, try_step

M = ('m',)


def letters(gs, neg):
    return paper.expand(gs) + ([M] if neg else [])


def reduced_db():
    """R1-R16 as (name, k, l, r)."""
    out = [('R1', 0, [M, M], [])]
    for i, ch in enumerate(paper.reduced_relations()):
        (lc, ln), (rc, rn) = ch
        l = letters(lc.gates(), ln)
        r = letters(rc.gates(), rn)
        k = max(paper.width(l), paper.width(r), lc.nw, rc.nw)
        out.append(('R%d' % (i + 2), k, l, r))
    return out


def normalise(name, k, l, r):
    """l scalar-free, r ending with its scalars."""
    lb, lp = strip_w(l)
    rb, rp = strip_w(r)
    return (name, k, lb, rb + [M] * ((lp + rp) % 2))


def frame(lines):
    return max([paper.width(letters(gs, n)) for _, gs, n in lines] + [1])


def labels_for(lab, known):
    """The equations a step label names (None: try everything)."""
    if lab is None or lab == '=':
        return None
    base = lab[1:] if lab.startswith('ML') else lab
    if base.startswith('L') and base[1:].isdigit():
        return [n for n in (base, 'M' + base) if n in known] or None
    if lab in known:
        return [lab]
    if lab == 'Def':
        return []
    if lab.replace('.', '').isdigit() and 'T' + lab in known:
        return ['T' + lab]
    return None


def derive_lines(lines, k, known, log=print, name=''):
    """A Deriv from the first line to the last, or (None, error)."""
    ws = [letters(gs, n) for _, gs, n in lines]
    labs = [lab for lab, _, _ in lines]
    # skip lines that do not denote the operator of the first one
    keep = [0]
    pending = []
    for i in range(1, len(ws)):
        if paper.same(ws[keep[-1]], ws[i], k):
            keep.append(i)
        else:
            log(f'  {name}: line {i} skipped (not the same operator)')
    d = Deriv(ws[0], k)
    prev = 0
    for idx in keep[1:]:
        tgt = ws[idx]
        names = []
        anyone = False
        for j in range(prev + 1, idx + 1):
            ls = labels_for(labs[j], known)
            if ls is None:
                anyone = True
            else:
                names += ls
        reorder_to_canon(d, ws[prev])
        if not step(d, names, tgt, anyone, known):
            return None, f'step to line {idx} ({labs[prev + 1:idx + 1]}) not found'
        prev = idx
    return d, None


def reorder_to_canon(d, target):
    """Reorder d's word to `target` if they are equal up to commuting
    letters (and scalars), else leave it."""
    a, ap = strip_w(d.word)
    b, bp = strip_w(target)
    if canon(a) == canon(b) and (ap - bp) % 2 == 0:
        d.reduce_phase()
        try:
            reorder_to(d, b + [M] * (ap % 2))
        except ValueError:
            pass


def step(d, names, tgt, anyone, known):
    a, ap = strip_w(d.word)
    b, bp = strip_w(tgt)
    if canon(a) == canon(b) and (ap - bp) % 2 == 0:
        return True
    if names and try_step(d, sorted(set(names), key=names.index), tgt):
        return True
    if solve_inv(d, tgt):
        return True
    if anyone or not names:
        if try_step(d, list(known), tgt):
            return True
    # two steps where the supplement wrote one
    if names:
        for n1 in names:
            saved = (list(d.word), list(d.steps))
            for mid in successors(d, n1):
                d.word, d.steps = list(mid[0]), list(mid[1])
                if try_step(d, sorted(set(names), key=names.index), tgt) or solve_inv(d, tgt):
                    return True
            d.word, d.steps = saved
    return False


def successors(d, name, cap=60):
    """Words one rewrite by `name` away from d (with their steps)."""
    out = []
    nm, k, l, r = engine.DB[engine.IDX[name]]
    for s in range(0, d.kmax - k + 1):
        for rev in (False, True):
            L, R = engine.shifted(l, s), engine.shifted(r, s)
            if rev:
                L, R = R, L
            Lb, Lp = strip_w(L)
            if not Lb:
                continue
            body, ph = strip_w(d.word)
            for dd, st in engine.gathers(body, Lb, d.kmax, limit=40):
                e = Deriv(list(d.word), d.kmax)
                e.steps = list(d.steps)
                try:
                    engine.reorder_body(e, dd.word)
                    if Lp:
                        e.ensure_phase(Lp)
                        e.phase_to_end()
                        for t in range(Lp):
                            e.mv(len(e.word) - 1, st + len(Lb) + t)
                    e.rw(nm, st, s, rev)
                    e.reduce_phase()
                    out.append((e.word, e.steps))
                except (AssertionError, ValueError):
                    pass
                if len(out) >= cap:
                    return out
    return out


def rev_word(w):
    return list(reversed(w))


def variants(name):
    """The equations x = rev(y) for x ++ y a rotation of the relator
    l ++ rev(r) of `name`, or of its reverse (every letter is an
    involution)."""
    n, k, l, r = engine.DB[engine.IDX[name]]
    rho_b, rho_p = strip_w(l + rev_word(r))
    out = []
    for flip, rho in ((0, rho_b), (1, rev_word(rho_b))):
        L = len(rho)
        for i in range(L):
            rot = rho[i:] + rho[:i]
            for j in range(1, L):
                x, y = rot[:j], rot[j:]
                vn = '%s@%d.%d.%d' % (name, flip, i, j)
                out.append((vn, k, x, rev_word(y) + [M] * (rho_p % 2)))
    return out


def ensure_variants(name, known):
    """Add the variants of `name` to the database; their names."""
    vs = [v for v in variants(name) if v[0] not in engine.IDX]
    if vs:
        engine.set_db(engine.DB + vs)
    return [v[0] for v in variants(name)]


_step = step


def step(d, names, tgt, anyone, known):
    if _step(d, names, tgt, anyone, known):
        return True
    vnames = []
    for n in (names or []):
        if '@' not in n:
            vnames += ensure_variants(n, known)
    if vnames and try_step(d, vnames, tgt):
        return True
    return False


MIRROR_LABEL = {'R6': 'R7', 'R7': 'R6', 'R8': 'R9', 'R9': 'R8', 'R10': 'R11', 'R11': 'R10',
                'R15': 'R16', 'R16': 'R15'}


def mirror_gate(g, k):
    """A parsed gate upside down in a frame of k wires."""
    if g[0] in ('H', 'Z', 'X'):
        return (g[0], k - 1 - g[1])
    if g[0] in ('CZ', 'CXZ'):
        return (g[0], k - 1 - g[1], k - 1 - g[2])
    if g[0] == 'box':
        ws = tuple(sorted(k - 1 - w for w in g[3]))
        return ('box', g[1], g[2], ws)
    raise ValueError(g)


def mirror_lines(lines, k):
    """A derivation upside down, its labels renamed accordingly."""
    out = []
    for lab, gs, n in lines:
        if lab in MIRROR_LABEL:
            lab = MIRROR_LABEL[lab]
        elif lab is not None and lab.startswith('L'):
            lab = 'M' + lab
        out.append((lab, [mirror_gate(g, k) for g in gs], n))
    return out


def neighbours(body, ph, names, kmax, limit=40):
    """Words one rewrite by one of `names` away (scalars counted mod 2)."""
    out = []
    for nm, s, rev in engine.candidates(names, kmax):
        e = engine.DB[engine.IDX[nm]]
        L, R = engine.shifted(e[2], s), engine.shifted(e[3], s)
        if rev:
            L, R = R, L
        Lb, Lp = strip_w(L)
        Rb, Rp = strip_w(R)
        if not Lb:
            continue
        nph = (ph - Lp + Rp) % 2
        for dd, st in engine.gathers(body, Lb, kmax, limit=limit):
            out.append((dd.word[:st] + Rb + dd.word[st + len(Lb):], nph))
    return out


def bridge(a, b, names, kmax, depth=3, cap=20000):
    """A path of words from a to b (up to commuting letters), each one
    rewrite by one of `names` from the last: meet in the middle."""
    def key(w, p):
        return (tuple(canon(w)), p)
    ab, ap = strip_w(a)
    bb, bp = strip_w(b)
    F = {key(ab, ap % 2): None}
    Fw = {key(ab, ap % 2): (ab, ap % 2)}
    B = {key(bb, bp % 2): None}
    Bw = {key(bb, bp % 2): (bb, bp % 2)}
    fr, br = [key(ab, ap % 2)], [key(bb, bp % 2)]
    for d in range(depth):
        for side in (0, 1):
            S, Sw, fr_ = (F, Fw, fr) if side == 0 else (B, Bw, br)
            nxt = []
            for kk in fr_:
                w, p = Sw[kk]
                for nw, np_ in neighbours(w, p, names, kmax):
                    k2 = key(nw, np_)
                    if k2 in S:
                        continue
                    S[k2] = kk
                    Sw[k2] = (nw, np_)
                    nxt.append(k2)
                    other = B if side == 0 else F
                    if k2 in other:
                        return _path(F, Fw, B, Bw, k2)
                if len(S) > cap:
                    break
            if side == 0:
                fr = nxt
            else:
                br = nxt
    return None


def _path(F, Fw, B, Bw, m):
    left = []
    k = m
    while k is not None:
        w, p = Fw[k]
        left.append(w + [M] * p)
        k = F[k]
    left.reverse()
    right = []
    k = B[m]
    while k is not None:
        w, p = Bw[k]
        right.append(w + [M] * p)
        k = B[k]
    return left + right


def follow(d, path, names):
    """Advance d along a path of words found by `bridge`."""
    for w in path[1:]:
        if not try_step(d, names, w):
            return False
    return True
