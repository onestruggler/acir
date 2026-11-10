"""Macro calculus over coloured placed gates on four wires.

A gate is (target, controls) with controls a sorted tuple of (wire, colour),
at most two of them: x_t += prod (x_c == colour).  Moves on words:
  narrow    a block on <= 3 wires (up to interchange of disjoint letters) is
            replaced by a shortest word with the same function  [(a)-steps]
  pair      adjacent g h spanning four wires with (g h)^2 = k, k the identity
            or a single gate: g h -> h g k  /  g h -> k h g   [pair lemma]
  expand    a gate k -> g h g h for a pair with (g h)^2 = k    [pair lemma]
The pair lemmas are 4-wire equations between <= 5 gates: rule (7) in every
placement and colouring, and eleven more orbits under the symmetries of the
cube, each derived from rule (7) by boot.py.
"""
import heapq
import itertools
import sys
import time
sys.dont_write_bytecode = True

WIRES = range(4)
GATES = []
for t in WIRES:
    others = [w for w in WIRES if w != t]
    GATES.append((t, ()))
    for c in others:
        for v in (1, 0):
            GATES.append((t, ((c, v),)))
    for a, b in itertools.combinations(others, 2):
        for va in (1, 0):
            for vb in (1, 0):
                GATES.append((t, ((a, va), (b, vb))))
NG = len(GATES)
GID = {g: i for i, g in enumerate(GATES)}
MASK = [sum(1 << w for w in [g[0]] + [c for c, _ in g[1]]) for g in GATES]


def gfunc(g):
    t, cs = g
    out = []
    for x in range(16):
        on = all(((x >> c) & 1) == v for c, v in cs)
        out.append(x ^ (1 << t) if on else x)
    return tuple(out)


F = [gfunc(g) for g in GATES]
ID = tuple(range(16))
FID = {f: i for i, f in enumerate(F)}


def func(w):
    p = list(range(16))
    for l in w:
        q = F[l]
        p = [q[v] for v in p]
    return tuple(p)


def gname(i):
    t, cs = GATES[i]
    return ''.join(('%d' if v else '~%d') % c for c, v in cs) + '>%d' % t


def show(w):
    return ' '.join(gname(l) for l in w) or 'e'


def gate(t, *cs):
    """gate(1, (0, 1), (3, 1)): target 1, black controls 0 and 3."""
    return GID[(t, tuple(sorted(cs)))]


def canon(w):
    """Lexicographically least linearisation of the trace of w."""
    w = list(w)
    out = []
    while w:
        best = None
        blocked = 0
        for i, l in enumerate(w):
            if not (MASK[l] & blocked):
                if best is None or l < w[best]:
                    best = i
            blocked |= MASK[l]
            if blocked == 15:
                break
        out.append(w.pop(best))
    return tuple(out)


TRIPLES = [7, 11, 13, 14]


def build_table(tm):
    gens = [i for i in range(NG) if not (MASK[i] & ~tm)]
    best = {ID: ()}
    frontier = [ID]
    while frontier:
        nxt = []
        for p in frontier:
            w = best[p]
            for g in gens:
                q = F[g]
                p2 = tuple(q[v] for v in p)
                if p2 not in best:
                    best[p2] = w + (g,)
                    nxt.append(p2)
        frontier = nxt
    return best


TABLE = {tm: build_table(tm) for tm in TRIPLES}


def narrow_once(w):
    """One shortening narrow step, or None.  Returns (new word, record)."""
    n = len(w)
    for tm in TRIPLES:
        for i in range(n):
            if MASK[w[i]] & ~tm:
                continue
            block = [i]
            blocked = 0
            for j in range(i + 1, n):
                m = MASK[w[j]]
                if (m & ~tm) or (m & blocked):
                    blocked |= m
                    if blocked & tm == tm:
                        break
                else:
                    block.append(j)
            if len(block) < 2:
                continue
            old = tuple(w[j] for j in block)
            new = TABLE[tm][func(old)]
            if len(new) < len(old):
                bs = set(block)
                rest = tuple(w[j] for j in range(i, n) if j not in bs)
                lin = tuple(w[:i]) + old + rest      # a linearisation of w
                res = tuple(w[:i]) + new + rest
                return res, {'kind': 'narrow', 'triple': [k for k in WIRES if tm >> k & 1],
                             'lin': list(lin), 'i': i, 'j': i + len(old), 'new': list(new)}
    return None


def normalise(w):
    steps = []
    w = canon(w)
    while True:
        r = narrow_once(w)
        if r is None:
            return w, steps
        w = canon(r[0])
        steps.append(r[1])


# ---- pair lemmas
PAIR = {}       # (g, h) -> k (gate id) or -1 for identity, when span is 4 wires
EXPAND = {}     # k -> list of (g, h)
for g in range(NG):
    for h in range(NG):
        if g == h or (MASK[g] | MASK[h]) != 15 or not (MASK[g] & MASK[h]):
            continue
        k = func((g, h, g, h))
        if k == ID:
            PAIR[(g, h)] = -1
        elif k in FID:
            PAIR[(g, h)] = FID[k]
            EXPAND.setdefault(FID[k], []).append((g, h))


def moves(w, expand=True):
    """Macro moves from the canonical word w: (new word, record)."""
    n = len(w)
    out = []
    for i in range(n):
        g = w[i]
        blocked = MASK[g]
        mid = []
        for j in range(i + 1, n):
            h = w[j]
            # h can be brought next to g if it is disjoint from the letters
            # between that share a wire (transitively) with g ... simple
            # sufficient test: h disjoint from every letter between
            if not any(MASK[l] & MASK[h] for l in mid):
                k = PAIR.get((g, h))
                if k is not None:
                    pre = tuple(w[:i])
                    post = tuple(mid) + tuple(w[j + 1:])
                    lin = pre + (g, h) + post
                    for m in ([(h, g)] if k == -1 else [(h, g, k), (k, h, g)]):
                        out.append((pre + m + post,
                                    {'kind': 'pair', 'lin': list(lin), 'i': i,
                                     'old': [g, h], 'new': list(m)}))
            mid.append(h)
            if len(mid) > 3:
                break
        if expand:
            for (a, b) in EXPAND.get(g, ()):
                out.append((tuple(w[:i]) + (a, b, a, b) + tuple(w[i + 1:]),
                            {'kind': 'expand', 'lin': list(w), 'i': i,
                             'old': [g], 'new': [a, b, a, b]}))
    return out


def check(lhs, rhs, steps):
    """Replay a macro derivation: every step preserves the function; narrow
    steps stay on their triple; lin is a linearisation of the current word;
    pair/expand steps are instances of the pair-lemma table."""
    cur = canon(lhs)
    f0 = func(lhs)
    assert f0 == func(rhs)
    for st in steps:
        lin = tuple(st['lin'])
        assert canon(lin) == cur, 'lin'
        i = st['i']
        if st['kind'] == 'narrow':
            tm = sum(1 << k for k in st['triple'])
            old = lin[i:st['j']]
            new = tuple(st['new'])
            assert bin(tm).count('1') <= 3
            assert all(not (MASK[l] & ~tm) for l in old + new)
            assert func(old) == func(new)
            cur = canon(lin[:i] + new + lin[st['j']:])
        else:
            old = tuple(st['old'])
            new = tuple(st['new'])
            assert lin[i:i + len(old)] == old and func(old) == func(new)
            if st['kind'] == 'pair':
                g, h = old
                k = PAIR[(g, h)]
                assert new in ([(h, g)] if k == -1 else [(h, g, k), (k, h, g)]) or \
                    tuple(new) in ([(h, g)] if k == -1 else [(h, g, k), (k, h, g)])
            else:
                assert (new[0], new[1]) in EXPAND[old[0]] and new[2:] == new[:2]
            cur = canon(lin[:i] + new + lin[i + len(old):])
        assert func(cur) == f0
    assert cur == canon(rhs), 'end'
    return True


def search(start, goal=(), max_states=600000, time_limit=300, wdepth=0.05,
           maxlen=None, expand=True, log=None):
    """Best-first reduction of `start` to `goal` (both normalised), bounded:
    at most `max_states` words are ever stored (a word stores its parent
    and the index of the move that made it, nothing else; the heap holds
    each stored word once), and the search stops after `time_limit`
    seconds.  Returns (steps or None, expansions, seconds, why)."""
    s0, st0 = normalise(start)
    g0, _ = normalise(goal)
    if maxlen is None:
        maxlen = len(s0) + 8
    parent = {s0: None}
    heap = [(len(s0), 0, s0)]
    t0 = time.time()
    n = 0
    full = False
    why = 'exhausted'
    while heap:
        if time.time() - t0 > time_limit:
            why = 'time limit'
            break
        pr, d, w = heapq.heappop(heap)
        if w == g0:
            path = []
            while parent[w] is not None:
                pw, k = parent[w]
                w2, rec = moves(pw, expand)[k]
                path.append((rec, normalise(w2)[1]))
                w = pw
            steps = list(st0)
            for rec, nst in reversed(path):
                steps.append(rec)
                steps.extend(nst)
            return steps, n, time.time() - t0, 'found'
        n += 1
        if log and n % 2000 == 0:
            log('  expanded %d, stored %d%s, len %d depth %d, %.0fs'
                % (n, len(parent), ' (full)' if full else '', len(w), d, time.time() - t0))
        if full:
            continue          # only words stored before the cap are expanded... no new ones
        for k, (w2, rec) in enumerate(moves(w, expand)):
            w3 = normalise(w2)[0]
            if len(w3) > maxlen or w3 in parent:
                continue
            parent[w3] = (w, k)
            heapq.heappush(heap, (len(w3) + wdepth * (d + 1), d + 1, w3))
            if len(parent) >= max_states:
                full = True
                why = 'state cap'
                break
        if full and g0 in parent:
            continue
        if full:
            break
    return None, n, time.time() - t0, why


if __name__ == '__main__':
    print(NG, 'gates;', len(PAIR), 'ordered pair lemmas;',
          sum(1 for v in PAIR.values() if v == -1), 'commuting')
