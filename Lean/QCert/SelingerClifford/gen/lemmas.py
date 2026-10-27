"""Derivations of the supplement's Lemmas 1.1-1.3: equations (4)-(10),
(14)-(18), (20) and (21), from the relations of Figure 8 and the lemmas
before them.

The supplement proves these as diagrams, labelled by the equations each
step uses but without the intermediate circuits.  So a proof is found by a
search guided by its labels (`derive2`: a meet-in-the-middle search whose
t-th layer applies the t-th label, one to three times), and where the proof
is long, the search runs between waypoints: intermediate circuits read off
the supplement's figures (checked numerically here before use).

Two of the supplement's labels are wrong: in the proof of (21) two steps
labelled (11) commute two CZs sharing a wire, which is (19), i.e. C12, and
the proof of Lemma 1.3 calls C12 "(19)".  `step_seg` falls back to C12 for
a single-label segment that its label cannot do, and reports it.
"""
from engine import DB, IDX, Deriv, canon, disj, reorder_to, same, shifted, \
    solve_inv, strip_w, try_step, gathers, candidates, w

# the supplement's labels and the equations they name
LAB = {
    '1': ['C1'], '2': ['C2'], '3': ['C3'], '4': ['L4'], '5': ['L5'], '6': ['L6'], '7': ['L7'],
    '8': ['L8'], '9': ['L9'], '10': ['L10'], '11': ['C5'], '12': ['C6', 'C7'],
    '13': ['C10', 'C11'], '14': ['L14', 'M14'], '15': ['L15', 'M15'], '16': ['L16', 'M16'],
    '17': ['L17', 'M17'], '18': ['L18', 'M18'], '19': ['C12'], 'C4': ['C4'],
    'C8': ['C8', 'C9'], 'C13': ['C13'], 'C14': ['C14', 'C15'], 'C15': ['C14', 'C15'],
}

REP = 3          # a layer applies its label one to REP times
NB_CAP = 4000    # at most this many words per layer and word


def key(body, ph):
    return (tuple(canon(body)), ph)


def ideals(word, cap=3000):
    """The splittings of word, up to commuting letters, as prefix ++ suffix."""
    n = len(word)
    out = []
    inc = [False] * n

    def dfs(i):
        if len(out) >= cap:
            return
        if i == n:
            out.append(([word[j] for j in range(n) if inc[j]],
                        [word[j] for j in range(n) if not inc[j]]))
            return
        if all(inc[j] or disj(word[i], word[j]) for j in range(i)):
            inc[i] = True
            dfs(i + 1)
            inc[i] = False
        dfs(i + 1)

    dfs(0)
    return out


def neighbours1(body, ph, names, kmax):
    """The words one rewrite by one of `names` away (a side without
    letters is inserted at every splitting)."""
    out = []
    for nm, s, rev in candidates(names, kmax):
        e = DB[IDX[nm]]
        L, R = shifted(e[2], s), shifted(e[3], s)
        if rev:
            L, R = R, L
        Lb, Lp = strip_w(L)
        Rb, Rp = strip_w(R)
        nph = (ph - Lp + Rp) % 8
        if not Lb:
            for pre, suf in ideals(body):
                out.append((pre + Rb + suf, nph))
            continue
        for dd, st in gathers(body, Lb, kmax, limit=200):
            out.append((dd.word[:st] + Rb + dd.word[st + len(Lb):], nph))
    return out


def neighbours_chain(body, ph, names, kmax):
    """The words one to REP rewrites away, each with the words on its way."""
    seen = {}
    frontier = [(body, ph, [])]
    for r in range(REP):
        nxt = []
        for b, p, ch in frontier:
            for nb, nph in neighbours1(b, p, names, kmax):
                k2 = key(nb, nph)
                if k2 not in seen:
                    c2 = ch + [nb + [w] * nph]
                    seen[k2] = (nb, nph, c2)
                    nxt.append((nb, nph, c2))
        frontier = nxt
        if len(seen) > NB_CAP:
            break
    return list(seen.values())


def search2(lhs, rhs, labels, kmax, cap=200000):
    """Words from lhs to rhs, the t-th layer by the t-th label: the
    sequence of words and the label of each step, or None."""
    lb, lp = strip_w(lhs)
    rb, rp = strip_w(rhs)
    n = len(labels)
    mid = n // 2

    def layers(start, labs):
        Ls = [{key(*start): (start[0], start[1], None, [])}]
        for lab in labs:
            nxt = {}
            for kk, (b, p, par, _) in Ls[-1].items():
                for nb, nph, ch in neighbours_chain(b, p, LAB[lab], kmax):
                    k2 = key(nb, nph)
                    if k2 not in nxt:
                        nxt[k2] = (nb, nph, kk, ch)
                if len(nxt) > cap:
                    break
            Ls.append(nxt)
        return Ls

    F = layers((lb, lp), labels[:mid])
    B = layers((rb, rp), list(reversed(labels[mid:])))
    meet = set(F[-1]) & set(B[-1])
    if not meet:
        return None
    m = min(meet)
    fsteps = []
    kk = m
    for t in range(len(F) - 1, 0, -1):
        b, p, par, ch = F[t][kk]
        fsteps.append((labels[t - 1], ch))
        kk = par
    fsteps.reverse()
    seq = [lhs]
    labs = []
    for lab, ch in fsteps:
        for wd in ch:
            seq.append(wd)
            labs.append(lab)
    kk = m
    for t in range(len(B) - 1, 0, -1):
        b, p, par, ch = B[t][kk]
        pb, pp, _, _ = B[t - 1][par]
        lab = labels[n - t]
        for wd in list(reversed(ch[:-1])) + [pb + [w] * pp]:
            seq.append(wd)
            labs.append(lab)
        kk = par
    return seq, labs


def derive2(lhs, rhs, labels, kmax):
    """(Deriv from lhs to rhs, None), or (None, error)."""
    r = search2(lhs, rhs, labels, kmax)
    if r is None:
        return None, 'no meet'
    seq, labs = r
    d = Deriv(lhs, kmax)
    for t in range(1, len(seq)):
        if not try_step(d, LAB[labs[t - 1]], seq[t]):
            return None, ('step failed', t, labs[t - 1])
    reorder_to(d, rhs)
    return d, None

# ------------------------------------------------------------------ data


def P(s):
    """'H1 Z0 S1 w' -> a word (Z i is the CZ of the wires i, i+1)."""
    out = []
    for t in s.split():
        if t == 'w':
            out.append(w)
        else:
            out.append((t[0], int(t[1:])))
    return out


# lemmas found by one search over the labels of their proofs
JOBS = {
    'L4': ['3', '2', 'C4'], 'L5': ['2', '4', '2'], 'L6': ['4', '2'], 'L7': ['6', '2', '3'],
    'L8': ['6', '5', '7'], 'L9': ['5', '5', '2'], 'L10': ['4', '3'],
    'L14': ['2', 'C8'],
    'L15': ['10', '12', '14', '5', '5', '2'],
}

# lemmas found by one search per segment between waypoints (None: the
# lemma's right side)
WAY = {
    'L16': [
        (['11', '13', '5', '12', '3'], P('H1 Z0 H1 S0 S1 Z0 H0 Z0')),
        (['13', '14', '12'],
         P('H1 Z0 H1 H0 Z0 S1 H0 S1 S0 S1 S0 S1 H0 S0 H0 S0 w w w w w w w')),
        (['3', '4', '3'], None),
    ],
    'L17': [
        (['12', '11', '13', 'C8'], P('Z0 H1 S0 S1 S0 S1 S0 H1 S1 H1 S1 Z0 H0 Z0 w w w w w w w')),
        (['4', '3', '13'], P('Z0 H1 S0 S1 S0 H1 S0 S0 H0 Z0 S1 S0 H0 S0 w w w w w w w')),
        (['3', '15', '7'], None),
    ],
}

# lemmas whose every step has a waypoint: one step per segment (`step_seg`)
STEPS = {
    'L18': [
        (['11'], P('H1 Z0 H1 H0 Z0 H1 Z0 Z0 H0 Z0')),
        (['13'], P('H1 Z0 H1 H0 S1 H1 Z0 S1 S0 H1 S1 Z0 H0 Z0 w w w w w w w')),
        (['15'], P('H1 Z0 S1 H0 H1 Z0 S1 S0 H1 S0 S1 S0 S1 H1 S1 H1 S1 Z0 H0 Z0 w w w w w w')),
        (['17'], P('Z0 S1 H0 H1 Z0 H1 S0 S1 S0 S1 S0 H1 H0 S1 S0 H1 S0 S1 S0 S1 S0 H1 S1 H1 S1 Z0'
                   ' H0 Z0 w w w w w w')),
        (['7'], P('Z0 S1 H0 H1 Z0 H1 S0 S1 S0 S1 S0 H1 H0 H1 S0 S1 S0 S1 S0 H1 S0 H1 S1 Z0 H0 Z0')),
        (['2'], P('Z0 S1 H0 H1 Z0 H1 S0 S1 S0 S1 S0 S1 H0 S1 S0 H1 S0 H1 S0 S1 S0 Z0 H0 Z0')),
        (['2'], P('Z0 S1 H0 H1 Z0 H1 S0 S1 S0 S1 S0 S1 H0 S1 S0 S1 S0 S0 S0 Z0 H0 Z0')),
        (['3'], P('Z0 S1 H0 H1 Z0 H1 S0 S1 S0 S0 H0 S0 S0 S0 S0 Z0 H0 Z0')),
        (['3'], P('Z0 S1 H0 H1 Z0 H1 S0 S1 S0 S0 H0 Z0 H0 Z0')),
        (['12'], P('Z0 S1 H0 H1 Z0 H1 S0 S0 S0 H0 Z0 S1 H0 Z0')),
        (['12'], P('Z0 S1 H0 H1 S0 S0 S0 Z0 H1 H0 Z0 S1 H0 Z0')),
        (['16'], P('Z0 H1 H0 S0 S0 S0 Z0 H1 H0 Z0 S1 H0 S0 H0 H0 Z0')),
        (['2'], P('Z0 H1 H0 S0 S0 S0 Z0 H1 H0 Z0 S1 H0 S0 Z0')),
        (['12'], P('Z0 H1 H0 S0 S0 S0 Z0 H1 H0 Z0 H0 Z0 S1 S0')),
        (['13'], P('Z0 H1 H0 S0 S0 S0 Z0 H1 H0 S0 H0 Z0 S1 S0 S1 H0 S0 S0 w w w w w w w')),
        (['12'], P('Z0 H1 H0 Z0 H1 S0 S0 S0 H0 S0 H0 Z0 S1 S0 S1 H0 S0 S0 w w w w w w w')),
        (['5'], P('Z0 H1 H0 Z0 H1 S0 S0 H0 S0 S0 S0 Z0 S1 S0 S1 H0 S0 S0')),
        (['12'], P('Z0 H1 H0 Z0 H1 S0 S0 H0 S0 S0 S0 S0 Z0 S1 H0 S1 S0 S0')),
        (['3'], P('Z0 H1 H0 Z0 H1 S0 S0 H0 Z0 S1 H0 S1 S0 S0')),
        (['14'], P('Z0 H1 H0 Z0 H1 H0 Z0 S1 H0 S1 S0 S1 S0 S1 H0 H0 S0 S0')),
        (['2'], P('Z0 H1 H0 Z0 H1 H0 Z0 S1 H0 S1 S0 S1 S0 S1 S0 S0')),
        (['3'], None),
    ],
    'L20': [
        (['2'], P('H1 H0 H1 H0 Z0 H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1')),
        (['11'], P('H1 H0 Z1 H0 Z1 H1 Z0 H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1')),
        (['2'], P('H1 H0 Z1 H0 H2 H1 H2 H1 Z1 H1 Z0 H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1')),
        (['11'], P('H1 H0 Z1 H0 H2 H1 Z1 Z1 H2 H1 Z1 H1 Z0 H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1')),
        (['C13'], P('H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1 H2 H1 H2 Z0 H1 H0 Z0 Z0 H1 H0 Z0 H1 Z1')),
        (['11'], P('H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1 H2 H1 H2 Z0 H1 H0 H1 H0 Z0 H1 Z1')),
        (['2'], P('H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1 H1 Z0 Z0 H1 Z1')),
        (['11'], P('H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1 H1 H1 Z1')),
        (['2'], P('H1 H0 Z1 H2 H1 Z1 H2 Z0 H1 H0 Z0 H1 Z1 Z1')),
        (['11'], None),
    ],
    'L21': [
        (['2'], P('Z0 H1 H0 Z1 H1 Z0 H1 H0 Z0 H1 H0 Z1 S1 H1 Z0 H1 H1')),
        (['3'], P('Z0 H1 H0 Z1 H1 Z0 H1 H0 Z0 H1 H0 Z1 S1 H1 Z0 H1 S0 S1 S0 S1 S0 S1 S0 S1 H1')),
        (['5'], P('Z0 H1 H0 Z1 H1 Z0 H1 H0 Z0 H1 H0 Z1 S1 H1 Z0 S1 S0 H1 S0 S1 S0 H1 S0 S1 H1'
                  ' w w w w w w w')),
        (['13'], P('Z0 H1 H0 Z1 H1 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 Z0 H1 S0 S1 S0 H1 S0')),
        (['19'], P('Z0 H1 H0 Z1 H1 Z0 H1 H0 Z0 H1 H0 Z0 Z1 H1 Z0 H1 S0 S1 S0 H1 S0')),
        (['18'], P('Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z0 Z1 H0 H1 Z0 H1 S0 S1 S0 H1 S0')),
        (['11'], P('Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 S0 S1 S0 H1 S0')),
        (['2'], P('Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 S1 H0 H1 S0 S0 S0')),
        (['11'], P('Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 H0 Z1 S0 S1 S0 H1 S0')),
        (['2'], P('H1 H0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 H0 Z1 S0 S1'
                  ' S0 H1 S0')),
        (['11'], P('H1 H0 Z0 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 Z0 H1 H0 Z0 H1 H0 Z1 H0 Z1'
                   ' S0 S1 S0 H1 S0')),
        (['C15'], None),
    ],
}

# labels whose steps cancel or insert involutions
GROUP = {'2', '3', '11'}

# ------------------------------------------------------------------ search


def step_seg(d, labels, target, log):
    """Advance d to the target by the labels: for a single label, by one
    step (or solve_inv for the involution labels), falling back to C12."""
    if len(labels) == 1:
        lab = labels[0]
        if lab in GROUP and solve_inv(d, target):
            return True
        if try_step(d, LAB[lab], target):
            return True
        if try_step(d, LAB['19'], target):
            log(f'  C12 used for a step labelled ({lab})')
            return True
    dd, err = derive2(d.word, target, labels, d.kmax)
    if err:
        return False
    d.replay(dd.steps)
    return True


def derive_lemma(nm, log=print):
    """(kmax, steps) for the lemma nm."""
    e = DB[IDX[nm]]
    k = max(e[1], 1)
    if nm in JOBS:
        d, err = derive2(e[2], e[3], JOBS[nm], k)
        if err:
            raise RuntimeError(f'{nm}: {err}')
        return k, d.steps
    segs = WAY.get(nm) or STEPS[nm]
    for labels, wp in segs:
        assert wp is None or same(e[2], wp, k), ('waypoint false', nm, wp)
    d = Deriv(e[2], k)
    for i, (labels, wp) in enumerate(segs):
        target = e[3] if wp is None else wp
        if nm in WAY:
            dd, err = derive2(d.word, target, labels, k)
            if err:
                raise RuntimeError(f'{nm}: segment {i}: {err}')
            d.replay(dd.steps)
        elif not step_seg(d, labels, target, log):
            raise RuntimeError(f'{nm}: segment {i} {labels} failed')
    reorder_to(d, e[3])
    return k, d.steps


ORDER = ['L4', 'L5', 'L6', 'L7', 'L8', 'L9', 'L10', 'L14', 'L15', 'L16', 'L17', 'L18', 'L20',
         'L21']


def derive_all(log=print):
    out = {}
    for nm in ORDER:
        out[nm] = derive_lemma(nm, log)
        log(f'lemma {nm}: {len(out[nm][1])} steps')
    return out
