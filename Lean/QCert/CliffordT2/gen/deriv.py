# Derivation search: rewriting certificates over a growing list of rules.
# A certificate step is (pos, ruleIndex, forward?) as checked by QCert.runSteps.
import sys, time
sys.path.insert(0, __import__('os').path.dirname(__file__))
from collections import deque

class Rules:
    def __init__(self):
        self.rules = []   # list of (lhs, rhs, name)
        self.index = {}   # name -> index
        self.proofs = {}  # name -> certificate (list of steps) or None for axioms
        self.uses = {}    # name -> list of names used
    def add(self, lhs, rhs, name, cert=None):
        assert name not in self.index, name
        self.index[name] = len(self.rules)
        self.rules.append((lhs, rhs, name))
        self.proofs[name] = cert
        return self.index[name]

def apply(w, rules, step):
    pos, k, d = step
    l, r, _ = rules[k]
    if not d: l, r = r, l
    assert w.startswith(l, pos), (w, step, l)
    return w[:pos] + r + w[pos + len(l):]

def replay(w, rules, steps):
    for s in steps: w = apply(w, rules, s)
    return w

def normalize(w, rules, allowed, maxsteps=100000):
    """Leftmost-first forward rewriting with the rules whose indices are in `allowed`
    (in that order of priority).  Returns the normal form and the steps."""
    steps = []
    for _ in range(maxsteps):
        done = True
        for i in range(len(w)):
            for k in allowed:
                l, r, _ = rules[k]
                if l and w.startswith(l, i):
                    steps.append((i, k, True))
                    w = w[:i] + r + w[i + len(l):]
                    done = False
                    break
            if not done: break
        if done: return w, steps
    raise Exception('normalize: too many steps')

def invert(steps, rules, w_start):
    """Steps from the end word back to w_start."""
    words = [w_start]
    for s in steps: words.append(apply(words[-1], rules, s))
    return [(p, k, not d) for (p, k, d) in reversed(steps)]

_IDX = {}
def _index(rules, moves):
    key = (id(rules), len(rules), tuple(moves))
    if key in _IDX: return _IDX[key]
    fw = {}; bw = {}; ins = []
    for k in moves:
        l, r, _ = rules[k]
        if l: fw.setdefault(l[0], []).append((k, l, r, True))
        if r: bw.setdefault(r[0], []).append((k, r, l, False))
        if r == '' and l: ins.append((k, l, False))
        if l == '' and r: ins.append((k, r, True))
    _IDX[key] = (fw, bw, ins)
    return _IDX[key]

def neighbors(w, rules, moves, maxlen):
    fw, bw, ins = _index(rules, moves)
    n = len(w)
    for i in range(n):
        c = w[i]
        for tab in (fw, bw):
            for (k, a, b, d) in tab.get(c, ()):
                if w.startswith(a, i):
                    nw = w[:i] + b + w[i + len(a):]
                    if len(nw) <= maxlen: yield nw, (i, k, d)
    for i in range(n + 1):
        for (k, a, d) in ins:
            if n + len(a) <= maxlen:
                yield w[:i] + a + w[i:], (i, k, d)
    return

def bisearch(u, v, rules, moves, maxlen=30, limit=200000, norm=None):
    """Bidirectional BFS from u and v; each visited word is normalized with `norm`
    (a list of rule indices, forward) if given.  Returns steps from u to v."""
    def nrm(w):
        if norm is None: return w, []
        return normalize(w, rules, norm)
    u0, su = nrm(u); v0, sv = nrm(v)
    if u0 == v0:
        return su + invert(sv, rules, v)
    # parent maps: word -> (prev word, step from prev to word)
    pu = {u0: None}; pv = {v0: None}
    qu = deque([u0]); qv = deque([v0])
    meet = None
    count = 0
    while qu and qv and meet is None and count < limit:
        for (q, P, Q) in ((qu, pu, pv), (qv, pv, pu)):
            for _ in range(len(q)):
                w = q.popleft(); count += 1
                for nw, st in neighbors(w, rules, moves, maxlen):
                    nw2, sn = nrm(nw)
                    if nw2 in P: continue
                    P[nw2] = (w, [st] + sn)
                    if nw2 in Q: meet = nw2; break
                    q.append(nw2)
                if meet is not None: break
            if meet is not None: break
    if meet is None: return None
    def path(P, w):
        out = []
        while P[w] is not None:
            prev, st = P[w]
            out = st + out
            w = prev
        return out
    # u -> u0 -> ... -> meet ; v -> v0 -> ... -> meet
    a = su + path(pu, meet)
    b = sv + path(pv, meet)
    # inverse of b: from meet back to v
    words = [v]
    for s in b: words.append(apply(words[-1], rules, s))
    binv = [(p, k, not d) for (p, k, d) in reversed(b)]
    return a + binv
