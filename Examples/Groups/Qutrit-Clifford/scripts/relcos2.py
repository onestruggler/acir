"""Proof-producing Todd-Coxeter (HLT with lookahead, coincidences) for
the cosets L·g of the local subgroup L in the two-qutrit Clifford group,
with the relators C1-C14 and the commutations.

A label k has a defining word defw[k]; an entry ent[k][x] = (lam, c, eq)
says defw[k] + x = lam + defw[c] (lam a local normal form), eq its
derivation (None when the two sides are the same string).  A dead label
b has parent[b] = (a, eq) with eq : defw[b] = mu + defw[a]."""
import sys, time
sys.setrecursionlimit(100000)
import relcos as RC
from kb import KB
S = RC.S
invw = RC.invw

# ---------------------------------------------------------------- local NF
UPIDX = {}
for i, d in RC.R0.items():
    e = S.eqs[i]
    src = (e['l'] if d > 0 else e['r']).translate(RC.UP)
    UPIDX.setdefault(src[0], []).append((i, d, src))
LOWIDX = {}
for i, d in RC.R0.items():
    e = S.eqs[i]
    src = e['l'] if d > 0 else e['r']
    LOWIDX.setdefault(src[0], []).append((i, d, src))

def rev(steps):
    return [(p, i, (d[1], d[0]) if i == 'P' else -d) for (p, i, d) in reversed(steps)]

def bubbleP(w):
    rank = {'n': 0, 'h': 1, 's': 1, 'H': 2, 'S': 2}
    t = ''.join(sorted(w, key=lambda ch: rank[ch]))
    return t, ([] if t == w else [(0, 'P', (w, t))])

def norm_idx(w, idx, up):
    steps = []
    while True:
        hit = None
        for p in range(len(w)):
            for i, d, src in idx.get(w[p], ()):
                if w.startswith(src, p):
                    hit = (p, i, d); break
            if hit: break
        if hit is None: return w, steps
        p, i, d = hit
        j = RC.lifted(i) if up else i
        steps.append((p, j, d))
        w = KB.apply(S, w, p, j, d)

MEMO = {}
import coset2 as C2
CANON1 = {}      # n-free uppercase word -> (j, Wc, steps W -> n^j Wc)
def canon_up(W):
    """W (over H S) = n^j Wc, Wc the shortlex-least word of its projective
    class, with a derivation through the one-qutrit normal form."""
    if W in CANON1: return CANON1[W]
    low = W.translate(str.maketrans('HS', 'hs'))
    M = C2.opmat(low)
    Wc = RC.ONE[RC.key1([[M[a][b] for b in range(3)] for a in range(3)])] if False else None
    from qt import mat as qmat
    M1 = qmat([{'h': ('H', 0), 's': ('S', 0)}[ch] for ch in reversed(low)], 1)
    wc = RC.ONE[RC.key1(M1)]
    for jj in range(6):
        M2 = qmat([('nu',)] * jj + [{'h': ('H', 0), 's': ('S', 0)}[ch] for ch in reversed(wc)], 1)
        if M2 == M1: break
    else:
        raise ValueError('scalar')
    Wc = wc.translate(RC.UP)
    n1, st1 = norm_idx(W, UPIDX, True)
    n2, st2 = norm_idx('n' * jj + Wc, UPIDX, True)
    assert n1 == n2, (W, n1, n2)
    CANON1[W] = (jj, Wc, st1 + rev(st2))
    return CANON1[W]

def lnorm(w):
    """n^k w0 Wc: Wc the canonical word of the wire-1 part's projective
    class, n^k w0 the one-qutrit normal form of the rest."""
    if w in MEMO: return MEMO[w]
    cur, steps = bubbleP(w)
    a = cur.count('n'); b = sum(1 for x in cur if x in 'hs')
    w0 = cur[a:a + b]; W1 = cur[a + b:]
    jj, Wc, st = canon_up(W1)
    steps = steps + [(p + a + b, i, d) for (p, i, d) in st]
    cur = cur[:a + b] + 'n' * jj + Wc
    cur2, st2 = bubbleP(cur)
    steps += st2; cur = cur2
    k = cur.count('n')
    seg = cur[:k + b]
    nf, st3 = norm_idx(seg, LOWIDX, False)
    steps += st3
    cur = nf + Wc
    while cur.startswith('n' * 6):
        steps.append((0, RC.AX['C1'], 1)); cur = cur[6:]
    MEMO[w] = (cur, steps)
    return cur, steps

def shift(steps, k):
    return [(p + k, i, d) for (p, i, d) in steps]


CANCEL = {}
ILAM = {}
def ilam(lam):
    """the normal form of the inverse of a local word"""
    if lam not in ILAM:
        ILAM[lam] = lnorm(invw(lam))[0]
    return ILAM[lam]

def cancel_eq(lam):
    """eq: ilam(lam) + lam = '' (by the local normal form)"""
    if lam not in CANCEL:
        il = ilam(lam)
        nf, st = lnorm(il + lam)
        assert nf == '', (lam, il, nf)
        CANCEL[lam] = S.lemma(il + lam, '', st)
    return CANCEL[lam]

# ---------------------------------------------------------------- labels
defw, ent, alive, parent = [], [], [], []

def add_label(w):
    j = len(defw)
    defw.append(w); ent.append({}); alive.append(True); parent.append(None)
    if w:
        ent[j]['n'] = ('n', j, S.lemma(w + 'n', 'n' + w, RC.move_n_left(w)))
    else:
        ent[j]['n'] = ('n', j, None)
    return j

def new_label(k, x):
    j = add_label(defw[k] + x)
    ent[k][x] = ('', j, None)
    return j

def eq_steps(start, p):
    return [] if p is None else [(0, p, 1)]

def resolve(k, x):
    lam, c, p = ent[k][x]
    while not alive[c]:
        a, q = parent[c]
        qr = S.eqs[q]['r']
        mu = qr[:len(qr) - len(defw[a])]
        steps = eq_steps(defw[k] + x, p)
        steps.append((len(lam), q, 1))
        nl, nst = lnorm(lam + mu)
        steps += nst
        eq = S.lemma(defw[k] + x, nl + defw[a], steps)
        lam, c, p = nl, a, eq
        ent[k][x] = (lam, c, p)
    return lam, c, p

def trace(c0, word):
    """steps: defw[c0] + word -> Lam + defw[c]"""
    lam = ''; c = c0; steps = []
    cur = defw[c0] + word
    for i, x in enumerate(word):
        l2, c2, p = resolve(c, x)
        if p is not None:
            steps.append((len(lam), p, 1))
        nl, nst = lnorm(lam + l2)
        steps += nst
        lam, c = nl, c2
    return steps, lam, c

def canon(b):
    """an alive label a and eq : defw[b] = mu + defw[a] (None if b alive)"""
    if alive[b]: return b, None
    a, q = parent[b]
    a2, q2 = canon(a)
    if q2 is None: return a, q
    # defw[b] = mu defw[a] = mu mu2 defw[a2]
    qr = S.eqs[q]['r']; mu = qr[:len(qr) - len(defw[a])]
    steps = [(0, q, 1), (len(mu), q2, 1)]
    q2r = S.eqs[q2]['r']; mu2 = q2r[:len(q2r) - len(defw[a2])]
    nl, nst = lnorm(mu + mu2)
    steps += nst
    eq = S.lemma(defw[b], nl + defw[a2], steps)
    parent[b] = (a2, eq)
    return a2, eq

def invert(eq, b, a):
    """from eq : defw[b] = mu defw[a], eq : defw[a] = mu' defw[b]"""
    qr = S.eqs[eq]['r']; mu = qr[:len(qr) - len(defw[a])]
    il = ilam(mu)
    steps = [(0, cancel_eq(mu), -1), (len(il), eq, -1)]
    return S.lemma(defw[a], il + defw[b], steps)

QUEUE = []
TARGET = {}
def coincide(b, a, eq):
    TARGET[eq] = a
    QUEUE.append((b, a, eq))

def run_queue():
    while QUEUE:
        b, a, eq = QUEUE.pop()
        do_merge(b, a, eq)

def do_merge(b, a, eq):
    # bring both to alive labels
    b2, qb = canon(b)
    if qb is not None:
        # defw[b] = mub defw[b2]; eq: defw[b] = mu defw[a] -> defw[b2] = ... defw[a]
        qbi = invert(qb, b, b2)      # defw[b2] = mub' defw[b]
        r = S.eqs[qbi]['r']; m1 = r[:len(r) - len(defw[b])]
        steps = [(0, qbi, 1), (len(m1), eq, 1)]
        r2 = S.eqs[eq]['r']; m2 = r2[:len(r2) - len(defw[a])]
        nl, nst = lnorm(m1 + m2)
        steps += nst
        eq = S.lemma(defw[b2], nl + defw[a], steps)
        b = b2
    a2, qa = canon(a)
    if qa is not None:
        r = S.eqs[eq]['r']; m1 = r[:len(r) - len(defw[a])]
        steps = [(0, eq, 1), (len(m1), qa, 1)]
        r2 = S.eqs[qa]['r']; m2 = r2[:len(r2) - len(defw[a2])]
        nl, nst = lnorm(m1 + m2)
        steps += nst
        eq = S.lemma(defw[b], nl + defw[a2], steps)
        a = a2
    if a == b: return
    if b < a:
        eq = invert(eq, b, a); a, b = b, a
    # kill b, keep a
    alive[b] = False; parent[b] = (a, eq)
    r = S.eqs[eq]['r']; mu = r[:len(r) - len(defw[a])]
    il = invw(mu)
    for x in list(ent[b].keys()):
        lam, c, p = resolve(b, x)
        steps = [(0, cancel_eq(mu), -1), (len(il), eq, -1)]
        if p is not None:
            steps.append((len(il), p, 1))
        nl, nst = lnorm(il + lam)
        steps += nst
        neq = S.lemma(defw[a] + x, nl + defw[c], steps)
        if x in ent[a]:
            la, ca, pa = resolve(a, x)
            if ca != c:
                il2 = invw(nl)
                st = [(0, cancel_eq(nl), -1), (len(il2), neq, -1)]
                if pa is not None:
                    st.append((len(il2), pa, 1))
                n2, ns2 = lnorm(il2 + la)
                st += ns2
                ceq = S.lemma(defw[c], n2 + defw[ca], st)
                coincide(c, ca, ceq)
        else:
            ent[a][x] = (nl, c, neq)

def relator_eq(a):
    RC.base_relator(a)
    return RC.RELATORS[(a, 0)]

RELS = [(a, RC.base_relator(a)) for a in list(RC.AX.values()) + list(RC.COMM.values())]
RELS.sort(key=lambda t: len(t[1]))

def scan(k, a, R):
    c = k; i = 0
    while i < len(R):
        x = R[i]
        if x not in ent[c]:
            if i == len(R) - 1: break
            new_label(c, x)
        _, c, _ = resolve(c, x)
        i += 1
    if i == len(R):
        if c != k:
            steps, lam, c2 = trace(k, R)
            il = invw(lam)
            st = [(0, cancel_eq(lam), -1)] + rev(shift(steps, len(il)))
            st.append((len(il) + len(defw[k]), relator_eq(a), 1))
            nl, nst = lnorm(il)
            st += nst
            ceq = S.lemma(defw[c2], nl + defw[k], st)
            coincide(c2, k, ceq)
            run_queue()
        return
    # deduce the last entry
    steps, lam, c = trace(k, R[:-1])
    x = R[-1]
    if x in ent[c]: return
    il = invw(lam)
    st = [(0, cancel_eq(lam), -1)] + rev(shift(steps, len(il)))
    st.append((len(il) + len(defw[k]), relator_eq(a), 1))
    nl, nst = lnorm(il)
    st += nst
    deq = S.lemma(defw[c] + x, nl + defw[k], st)
    ent[c][x] = (nl, k, deq)

def enumerate_cosets(limit=200000, timeout=3600):
    t0 = time.time()
    add_label('')
    for x in 'hsHS':
        ent[0][x] = (x, 0, None)
    k = 0
    while k < len(defw):
        if alive[k]:
            for a, R in RELS:
                if not alive[k]: break
                scan(k, a, R)
        k += 1
        if k % 50 == 0:
            print('label', k, 'of', len(defw), 'alive', sum(alive), 'eqs', len(S.eqs),
                  '%.0fs' % (time.time() - t0), file=sys.stderr)
        if len(defw) > limit or time.time() - t0 > timeout:
            return False
    # fill: every alive label has all letters
    return all(all(x in ent[j] for x in 'nhsHSc') for j in range(len(defw)) if alive[j])

if __name__ == '__main__':
    ok = enumerate_cosets()
    print('done' if ok else 'INCOMPLETE', 'alive', sum(alive), 'labels', len(defw), 'eqs', len(S.eqs), file=sys.stderr)
