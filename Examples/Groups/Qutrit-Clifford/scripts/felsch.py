"""Felsch-style proof-producing coset enumeration (two qutrits), on the
machinery of relcos2: deductions first, a new label only when none is
pending, coincidences merged with their derivations."""
import sys, time
import relcos2 as T
import relcos as RC
S = T.S
invw, rev, shift, lnorm = T.ilam, T.rev, T.shift, T.lnorm

INV = {}        # (c, x) -> set of labels k with ent[k][x] = (_, c, _)
QUEUE = []      # deductions to process: (k, x)
COIN = []       # coincidences to process: (b, a, eq)

def set_entry(k, x, lam, c, eq):
    T.ent[k][x] = (lam, c, eq)
    INV.setdefault((c, x), set()).add(k)
    QUEUE.append((k, x))

def add_label(w):
    j = len(T.defw)
    T.defw.append(w); T.ent.append({}); T.alive.append(True); T.parent.append(None)
    if w:
        set_entry(j, 'n', 'n', j, S.lemma(w + 'n', 'n' + w, RC.move_n_left(w)))
    else:
        set_entry(j, 'n', 'n', j, None)
    return j

def define(k, x):
    j = add_label(T.defw[k] + x)
    set_entry(k, x, '', j, None)
    return j

def target(k, x):
    """the alive target of a known entry (resolving, keeping INV right)"""
    lam, c, p = T.ent[k][x]
    if not T.alive[c]:
        old = c
        lam, c, p = T.resolve(k, x)
        INV.get((old, x), set()).discard(k)
        INV.setdefault((c, x), set()).add(k)
    return c

def sources(c, x):
    """alive labels k with ent[k][x] targeting c"""
    out = []
    for k in list(INV.get((c, x), ())):
        if not T.alive[k]:
            INV[(c, x)].discard(k); continue
        if target(k, x) == c:
            out.append(k)
    return out

def relator_eq_rot(a, rho):
    return RC.relator(a, rho)

def cycle_proof(start, a, rho, upto):
    """trace the rotation rho of relator a from start over its first
    'upto' letters, with the proof"""
    R = RC.base_relator(a)
    Rr = R[rho:] + R[:rho]
    return T.trace(start, Rr[:upto]), Rr

def deduce(start, a, rho):
    (steps, lam, c), Rr = cycle_proof(start, a, rho, len(RC.base_relator(a)) - 1)
    x = Rr[-1]
    if x in T.ent[c]:
        return
    il = invw(lam)
    st = [(0, T.cancel_eq(lam), -1)] + rev(shift(steps, len(il)))
    st.append((len(il) + len(T.defw[start]), relator_eq_rot(a, rho), 1))
    nl, nst = lnorm(il)
    st += nst
    eq = S.lemma(T.defw[c] + x, nl + T.defw[start], st)
    set_entry(c, x, nl, start, eq)

def coincidence(start, a, rho, end):
    (steps, lam, c2), Rr = cycle_proof(start, a, rho, len(RC.base_relator(a)))
    il = invw(lam)
    st = [(0, T.cancel_eq(lam), -1)] + rev(shift(steps, len(il)))
    st.append((len(il) + len(T.defw[start]), relator_eq_rot(a, rho), 1))
    nl, nst = lnorm(il)
    st += nst
    eq = S.lemma(T.defw[c2], nl + T.defw[start], st)
    COIN.append((c2, start, eq))

def merge(b, a, eq):
    """eq : defw[b] = mu defw[a]"""
    b2, qb = T.canon(b)
    if qb is not None:
        qbi = T.invert(qb, b, b2)
        r = S.eqs[qbi]['r']; m1 = r[:len(r) - len(T.defw[b])]
        steps = [(0, qbi, 1), (len(m1), eq, 1)]
        r2 = S.eqs[eq]['r']; m2 = r2[:len(r2) - len(T.defw[a])]
        nl, nst = lnorm(m1 + m2)
        eq = S.lemma(T.defw[b2], nl + T.defw[a], steps + nst)
        b = b2
    a2, qa = T.canon(a)
    if qa is not None:
        r = S.eqs[eq]['r']; m1 = r[:len(r) - len(T.defw[a])]
        steps = [(0, eq, 1), (len(m1), qa, 1)]
        r2 = S.eqs[qa]['r']; m2 = r2[:len(r2) - len(T.defw[a2])]
        nl, nst = lnorm(m1 + m2)
        eq = S.lemma(T.defw[b], nl + T.defw[a2], steps + nst)
        a = a2
    if a == b: return
    if b < a:
        eq = T.invert(eq, b, a); a, b = b, a
    T.alive[b] = False; T.parent[b] = (a, eq)
    r = S.eqs[eq]['r']; mu = r[:len(r) - len(T.defw[a])]
    il = invw(mu)
    # entries into b now go to a
    for x in 'nhsHSc':
        for k in list(INV.get((b, x), ())):
            if T.alive[k] and x in T.ent[k]:
                target(k, x)
                QUEUE.append((k, x))
        INV.pop((b, x), None)
    # entries out of b move to a
    for x in list(T.ent[b].keys()):
        lam, c, p = T.resolve(b, x)
        INV.get((c, x), set()).discard(b)
        steps = [(0, T.cancel_eq(mu), -1), (len(il), eq, -1)]
        if p is not None:
            steps.append((len(il), p, 1))
        nl, nst = lnorm(il + lam)
        neq = S.lemma(T.defw[a] + x, nl + T.defw[c], steps + nst)
        if x in T.ent[a]:
            ca = target(a, x)
            la, ca, pa = T.ent[a][x]
            if ca != c:
                il2 = invw(nl)
                st = [(0, T.cancel_eq(nl), -1), (len(il2), neq, -1)]
                if pa is not None:
                    st.append((len(il2), pa, 1))
                n2, ns2 = lnorm(il2 + la)
                ceq = S.lemma(T.defw[c], n2 + T.defw[ca], st + ns2)
                COIN.append((c, ca, ceq))
        else:
            set_entry(a, x, nl, c, neq)

RELS = T.RELS
POS = {}        # letter -> [(a, R, i)]
for a, R in RELS:
    for i, x in enumerate(R):
        POS.setdefault(x, []).append((a, R, i))

def process(k, x):
    if not T.alive[k] or x not in T.ent[k]: return
    for a, R, i in POS.get(x, ()):
        if not T.alive[k]: return
        L = len(R)
        # forward from k, starting with letter i
        f = k; fi = 0
        while fi < L:
            y = R[(i + fi) % L]
            if y not in T.ent[f]: break
            f = target(f, y); fi += 1
        if fi == L:
            if f != k:
                coincidence(k, a, i, f)
            continue
        # backward from k over R[i-1], R[i-2], ...
        b = k; bi = 0
        while bi < L - fi:
            y = R[(i - 1 - bi) % L]
            src = sources(b, y)
            if not src: break
            b = src[0]; bi += 1
        if fi + bi == L - 1:
            deduce(b, a, (i - bi) % L)
        elif fi + bi >= L:
            pass

def run(limit=20000, timeout=3600):
    t0 = time.time()
    add_label('')
    for x in 'hsHS':
        set_entry(0, x, x, 0, None)
    while True:
        while QUEUE or COIN:
            while COIN:
                b, a, eq = COIN.pop()
                merge(b, a, eq)
            if QUEUE:
                k, x = QUEUE.pop()
                process(k, x)
        gap = next(((k, x) for k in range(len(T.defw)) if T.alive[k]
                    for x in 'nhsHSc' if x not in T.ent[k]), None)
        if gap is None: break
        define(*gap)
        if len(T.defw) > limit or time.time() - t0 > timeout:
            return False
    print('labels', len(T.defw), 'alive', sum(T.alive), 'eqs', len(S.eqs),
          '%.0fs' % (time.time() - t0), file=sys.stderr)
    return True

if __name__ == '__main__':
    print('done' if run() else 'INCOMPLETE', file=sys.stderr)
