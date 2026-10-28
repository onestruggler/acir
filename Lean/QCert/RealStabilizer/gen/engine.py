"""The database of equations and the step finder (adapted from the
Selinger generator, `SelingerClifford/gen/engine.py`).

Letters: ('m',) the scalar -1, ('H', i), ('Z', i), ('C', i) the CZ of the
wires i, i+1, in time order.  A derivation is a list of checker steps,
exactly as `Step` of `Rewrite.lean`: ('mv', i, j) moves the letter at i to
j past letters on disjoint wires, and ('rw', e, pos, s, rev) replaces, at
position pos, the left side of equation e shifted s wires up by its right
side (the other way round if rev).

The database DB is a list of (name, k, l, r): l = r on k wires, l without
scalars, r ending with its scalars; it is filled by the driver.
"""
from collections import deque

w = ('m',)


def wires(a):
    if a[0] == 'm':
        return ()
    if a[0] == 'C':
        return (a[1], a[1] + 1)
    return (a[1],)


def disj(a, b):
    return not (set(wires(a)) & set(wires(b)))


def key(a):
    order = {'m': 0, 'Z': 1, 'H': 2, 'C': 3}
    return (wires(a)[0] if wires(a) else -1, order[a[0]])


def canon(word):
    """The least word equal to `word` up to commuting letters."""
    rest = list(word)
    out = []
    while rest:
        best = None
        for idx, a in enumerate(rest):
            if all(disj(a, b) for b in rest[:idx]):
                if best is None or key(a) < key(rest[best]):
                    best = idx
        out.append(rest.pop(best))
    return out


DB = []
IDX = {}


def set_db(db):
    DB[:] = db
    IDX.clear()
    for i, e in enumerate(DB):
        IDX[e[0]] = i


def shifted(word, s):
    return [a if a[0] == 'm' else (a[0], a[1] + s) for a in word]


def strip_w(word):
    """The letters other than the scalar, and the number of scalars."""
    return [a for a in word if a[0] != 'm'], sum(1 for a in word if a[0] == 'm')

# ------------------------------------------------------------ derivations


class Deriv:
    """A word under derivation on kmax wires, and the steps so far."""

    def __init__(self, word, kmax):
        self.word = list(word)
        self.kmax = kmax
        self.steps = []

    def mv(self, i, j):
        if i == j:
            return
        a = self.word[i]
        if i < j:
            u = self.word[i + 1:j + 1]
            assert all(disj(a, b) for b in u), ('mv', i, j)
            self.word = self.word[:i] + u + [a] + self.word[j + 1:]
        else:
            u = self.word[j:i]
            assert all(disj(a, b) for b in u), ('mv', i, j)
            self.word = self.word[:j] + [a] + u + self.word[i + 1:]
        self.steps.append(('mv', i, j))

    def rw(self, name, pos, s, rev):
        e = IDX[name]
        nm, k, l, r = DB[e]
        assert k + s <= self.kmax, (name, s)
        L, R = shifted(l, s), shifted(r, s)
        if rev:
            L, R = R, L
        assert self.word[pos:pos + len(L)] == L, ('rw', name, pos)
        self.word = self.word[:pos] + R + self.word[pos + len(L):]
        self.steps.append(('rw', e, pos, s, rev))

    def replay(self, steps):
        for st in steps:
            if st[0] == 'mv':
                self.mv(st[1], st[2])
            else:
                _, ei, pos, sh, rev = st
                self.rw(DB[ei][0], pos, sh, rev)

    def nphase(self):
        return sum(1 for a in self.word if a[0] == 'm')

    def phase_to_end(self):
        """Move every scalar to the end."""
        idxs = [i for i, a in enumerate(self.word) if a[0] == 'm']
        target = len(self.word) - 1
        for i in reversed(idxs):
            self.mv(i, target)
            target -= 1

    def reduce_phase(self):
        """Scalars to the end, and (-1)^2 removed by R1."""
        self.phase_to_end()
        while self.nphase() >= 2:
            self.rw('R1', len(self.word) - 2, 0, False)

    def ensure_phase(self, m):
        """At least m scalars (inserting (-1)^2 by R1)."""
        if self.nphase() < m:
            self.rw('R1', len(self.word), 0, True)


def candidates(names, kmax):
    for nm in names:
        k = DB[IDX[nm]][1]
        for s in range(0, kmax - k + 1):
            for rev in (False, True):
                yield nm, s, rev


def reorder_to(d, target):
    """Move letters so that the word is exactly target (equal up to
    commuting letters)."""
    for t in range(len(target)):
        if d.word[t] == target[t]:
            continue
        for p in range(t + 1, len(d.word)):
            if d.word[p] == target[t] and all(disj(d.word[p], d.word[q]) for q in range(t, p)):
                d.mv(p, t)
                break
        else:
            raise ValueError('reorder failed at %d' % t)
    assert d.word == target


def reorder_body(d, body):
    """Reorder the word, its scalars at the end, so that the rest is body."""
    ph = d.nphase()
    d.phase_to_end()
    reorder_to(d, body + [w] * ph)

# ------------------------------------------------------- finding a pattern


def trace_embeddings(word, L, cap=5000):
    """Increasing position lists P such that the letters of word at P are
    L up to commuting letters, and every letter skipped between them can be
    moved out of the way."""
    n, m = len(word), len(L)
    dep = [[j for j in range(i) if not disj(L[i], L[j])] for i in range(m)]
    sols = []
    matched = [False] * m
    chosen = []

    def dfs(p, cnt):
        if len(sols) >= cap:
            return
        if cnt == m:
            sols.append(list(chosen))
            return
        if p >= n:
            return
        if n - p < m - cnt:
            return
        x = word[p]
        for i in range(m):
            if matched[i] or L[i] != x:
                continue
            if all(matched[j] for j in dep[i]):
                matched[i] = True
                chosen.append(p)
                dfs(p + 1, cnt + 1)
                chosen.pop()
                matched[i] = False
                break
        if cnt == 0:
            dfs(p + 1, cnt)
        elif x[0] == 'm' or all(disj(x, word[c]) for c in chosen) or \
                all(disj(x, L[i]) for i in range(m) if not matched[i]):
            dfs(p + 1, cnt)

    dfs(0, 0)
    return sols


def try_gather(d, sol):
    """Make the letters at the positions sol contiguous by moves; returns
    the start of the block, or None (and d unchanged)."""
    saved = (list(d.word), list(d.steps))
    try:
        pos = list(sol)
        for t in range(1, len(pos)):
            while pos[t] != pos[t - 1] + 1:
                a = d.word[pos[t]]
                gap = range(pos[t - 1] + 1, pos[t])
                if all(disj(a, d.word[c]) for c in gap):
                    d.mv(pos[t], pos[t - 1] + 1)
                    pos[t] = pos[t - 1] + 1
                    continue
                q = pos[t - 1] + 1
                b = d.word[q]
                if all(disj(b, d.word[c]) for c in range(pos[0], pos[t - 1] + 1)):
                    d.mv(q, pos[0])
                    for u in range(t):
                        pos[u] += 1
                elif all(disj(b, d.word[c]) for c in range(q + 1, pos[t] + 1)):
                    d.mv(q, pos[t])
                    pos[t] -= 1
                else:
                    raise ValueError('blocked')
        return pos[0]
    except (ValueError, AssertionError):
        d.word, d.steps = saved
        return None


GATHER_LIMIT = [400]


def gathers(word, L, kmax, limit=None):
    """Yield (Deriv, start) for each way found to bring the letters L
    together, in that order, in word."""
    lim = GATHER_LIMIT[0] if limit is None else limit
    seen = set()
    sols = trace_embeddings(word, L, cap=20000 if lim > 400 else 5000)
    sols.sort(key=lambda sl: sl[-1] - sl[0])
    for sol in sols[:lim]:
        key_ = tuple(sol)
        if key_ in seen:
            continue
        seen.add(key_)
        d = Deriv(word, kmax)
        st = try_gather(d, sol)
        if st is None:
            continue
        try:
            for t in range(len(L)):
                if d.word[st + t] == L[t]:
                    continue
                for p in range(st + t + 1, st + len(L)):
                    if d.word[p] == L[t] and all(disj(d.word[p], d.word[q]) for q in range(st + t, p)):
                        d.mv(p, st + t)
                        break
                else:
                    raise ValueError
        except (ValueError, AssertionError):
            continue
        yield d, st

# ------------------------------------------------------------- one step


def _apply_at(d, u, p, nm, s, rev, Lb, Lp):
    """Reorder d to the body u, bring Lp scalars after the pattern at p, and
    rewrite there."""
    reorder_body(d, u)
    if Lp:
        d.ensure_phase(Lp)
        d.phase_to_end()
        for t in range(Lp):
            d.mv(len(d.word) - 1, p + len(Lb) + t)
    d.rw(nm, p, s, rev)
    d.reduce_phase()


def _sides(nm, s, rev):
    e = DB[IDX[nm]]
    L, R = shifted(e[2], s), shifted(e[3], s)
    if rev:
        L, R = R, L
    return strip_w(L), strip_w(R)


def _try_target(d, names, target):
    """Target-driven: find the rewritten side in the target, and the word it
    came from in the current word."""
    tgt_body, tgt_ph = strip_w(target)
    tgt_c = canon(tgt_body)
    cur_body, cur_ph = strip_w(d.word)
    cur_c = canon(cur_body)
    for nm, s, rev in candidates(names, d.kmax):
        (Lb, Lp), (Rb, Rp) = _sides(nm, s, rev)
        if not Lb and not Rb:
            continue
        if (cur_ph - Lp + Rp - tgt_ph) % 2:
            continue
        if not Rb:
            occ = [(tgt_body, p) for p in range(len(tgt_body) + 1)]
        else:
            occ = [(dd.word, st) for dd, st in gathers(tgt_body, Rb, d.kmax)]
        for t2, p in occ:
            u = t2[:p] + Lb + t2[p + len(Rb):]
            if canon(u) != cur_c:
                continue
            saved = (list(d.word), list(d.steps))
            try:
                _apply_at(d, u, p, nm, s, rev, Lb, Lp)
                nb, nph = strip_w(d.word)
                if canon(nb) == tgt_c and (nph - tgt_ph) % 2 == 0:
                    return True
            except (AssertionError, ValueError):
                pass
            d.word, d.steps = saved
    return False


def _try_forward(d, names, target):
    """Forward: rewrite an occurrence of a left side in the current word."""
    tgt_body, tgt_ph = strip_w(target)
    tgt_c = canon(tgt_body)
    for nm, s, rev in candidates(names, d.kmax):
        (Lb, Lp), (Rb, Rp) = _sides(nm, s, rev)
        if not Lb:
            continue
        cur_body, cur_ph = strip_w(d.word)
        if (cur_ph - Lp + Rp - tgt_ph) % 2:
            continue
        for dd, st in gathers(cur_body, Lb, d.kmax):
            saved = (list(d.word), list(d.steps))
            try:
                _apply_at(d, dd.word, st, nm, s, rev, Lb, Lp)
                nb, nph = strip_w(d.word)
                if canon(nb) == tgt_c and (nph - tgt_ph) % 2 == 0:
                    return True
            except (AssertionError, ValueError):
                pass
            d.word, d.steps = saved
    return False


def _try_forward_cleanup(d, names, target):
    """Forward, then cancel or insert involutions (solve_inv) to reach the
    target: for a line whose step also cancels letters."""
    tgt_body, tgt_ph = strip_w(target)
    for nm, s, rev in candidates(names, d.kmax):
        (Lb, Lp), (Rb, Rp) = _sides(nm, s, rev)
        if not Lb:
            continue
        cur_body, cur_ph = strip_w(d.word)
        if (cur_ph - Lp + Rp - tgt_ph) % 2:
            continue
        for dd, st in gathers(cur_body, Lb, d.kmax, limit=3000):
            saved = (list(d.word), list(d.steps))
            try:
                _apply_at(d, dd.word, st, nm, s, rev, Lb, Lp)
                nb, nph = strip_w(d.word)
                if abs(len(nb) - len(tgt_body)) <= 8 and solve_inv(d, target):
                    return True
            except (AssertionError, ValueError):
                pass
            d.word, d.steps = saved
    return False


def try_step(d, names, target):
    """One rewrite by one of the equations `names` taking d to the target
    (up to commuting letters and (-1)^2); commits and returns True."""
    for lim in (400, 20000):
        GATHER_LIMIT[0] = lim
        ok = _try_target(d, names, target) or _try_forward(d, names, target)
        GATHER_LIMIT[0] = 400
        if ok:
            return True
    return _try_forward_cleanup(d, names, target)

# ----------------------------------------------- cancelling involutions


def removals(cur):
    """Removable pairs: (positions, letter, rule) for [g, g] with g an H, Z
    or CZ, up to commuting letters."""
    n = len(cur)
    for j in range(n):
        g = cur[j]
        if g[0] in ('H', 'Z', 'C'):
            for i in range(j - 1, -1, -1):
                if cur[i] == g:
                    if all(disj(g, cur[t]) for t in range(i + 1, j)):
                        yield (i, j), g, {'H': 'R3', 'Z': 'R2', 'C': 'R5'}[g[0]]
                    break
                if not disj(g, cur[i]):
                    break


def pair_path(big, small, maxnodes=300000):
    """Words from big to a word equal to small up to commuting letters, each
    by removing one group; breadth first."""
    target = canon(small)
    start = list(big)
    if canon(start) == target:
        return [start]
    prev = {tuple(canon(start)): None}
    words = {tuple(canon(start)): start}
    q = deque([start])
    while q:
        cur = q.popleft()
        if len(cur) <= len(small):
            continue
        for pos, g, rule in removals(cur):
            nxt = [cur[t] for t in range(len(cur)) if t not in pos]
            key_ = tuple(canon(nxt))
            if key_ in prev:
                continue
            prev[key_] = tuple(canon(cur))
            words[key_] = nxt
            if list(key_) == target:
                path = [nxt]
                kk = tuple(canon(cur))
                while kk is not None:
                    path.append(words[kk])
                    kk = prev[kk]
                return list(reversed(path))
            q.append(nxt)
            if len(prev) > maxnodes:
                return None
    return None


def _group_diff(short, long_):
    for pos, g, rule in removals(long_):
        rest = [long_[t] for t in range(len(long_)) if t not in pos]
        if canon(rest) == canon(short):
            return rest, pos, g, rule
    raise ValueError('group diff')


def _insert_group(d, rest, pos, g, rule):
    reorder_body(d, rest)
    d.rw(rule, pos[0], g[1], True)
    for t in range(len(pos) - 1, 0, -1):
        d.mv(pos[0] + t, pos[t])


def _remove_group(d, cur, pos, g, rule):
    reorder_body(d, cur)
    for t in range(1, len(pos)):
        d.mv(pos[t], pos[0] + t)
    d.rw(rule, pos[0], g[1], False)


def solve_inv(d, target):
    """Reach the target by inserting or removing the groups of `removals`
    (the supplement's step "inv"); commits and returns True."""
    a, aph = strip_w(d.word)
    b, bph = strip_w(target)
    insert = len(b) >= len(a)
    big, small = (b, a) if insert else (a, b)
    path = pair_path(big, small)
    if path is None:
        return False
    saved = (list(d.word), list(d.steps))
    try:
        if insert:
            seq = list(reversed(path))
            for t in range(len(seq) - 1):
                rest, pos, g, rule = _group_diff(seq[t], seq[t + 1])
                _insert_group(d, rest, pos, g, rule)
        else:
            for t in range(len(path) - 1):
                rest, pos, g, rule = _group_diff(path[t + 1], path[t])
                _remove_group(d, path[t], pos, g, rule)
        nb, nph = strip_w(d.word)
        if canon(nb) == canon(b):
            return True
    except (AssertionError, ValueError):
        pass
    d.word, d.steps = saved
    return False
