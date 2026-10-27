# Two-wire real-Clifford+CH words, OPERATOR order (leftmost letter applied last).
# Letters: h z (wire 0), H Z (wire 1), C (CZ), K (CH: control wire 1, H on wire 0), S (swap, eq. (8)).
import numpy as np, collections, time
s2 = 1/np.sqrt(2)
Hm = np.array([[s2,s2],[s2,-s2]]); Zm = np.diag([1.,-1.]); I2 = np.eye(2)
SWm = np.zeros((4,4))
for i in range(4): SWm[((i&1)<<1)|(i>>1), i] = 1
Km = np.eye(4); Km[2:,2:] = Hm
MAT = {'h': np.kron(I2,Hm), 'z': np.kron(I2,Zm), 'H': np.kron(Hm,I2), 'Z': np.kron(Zm,I2),
       'C': np.diag([1.,1,1,-1]), 'K': Km, 'S': SWm}
def sem(w):
    M = np.eye(4)
    for c in w: M = M @ MAT[c]
    return M
def eq(a, b): return np.allclose(sem(a), sem(b))
def drawn(*parts): return ''.join(reversed(parts))
W0 = set('hz'); W1 = set('HZ'); SEP = set('CKS')
def canon(w):
    out = []; x = []; y = []
    for c in w:
        if c in SEP: out.append(''.join(y)+''.join(x)); out.append(c); x=[]; y=[]
        elif c in W0: x.append(c)
        else: y.append(c)
    out.append(''.join(y)+''.join(x))
    return ''.join(out)
def blocks(w):
    bl = []; seps = []; x = []; y = []
    for c in w:
        if c in SEP: bl.append((''.join(x), ''.join(y))); seps.append(c); x=[]; y=[]
        elif c in W0: x.append(c)
        else: y.append(c)
    bl.append((''.join(x), ''.join(y)))
    return bl, seps
def unblocks(bl, seps):
    out = []
    for i,(x,y) in enumerate(bl):
        out.append(y+x)
        if i < len(seps): out.append(seps[i])
    return ''.join(out)
def finds(s, a):
    if a == '': return list(range(len(s)+1))
    r = []; st = 0
    while True:
        p = s.find(a, st)
        if p < 0: return r
        r.append(p); st = p+1
def matches(w, l):
    """(u, v) with canon(u + l + v) == w; w, l canonical"""
    B, S = blocks(w); A, T = blocks(l); k = len(T)
    if k == 0:
        a, b = A[0]
        if a == '' and b == '': return
        for i,(x,y) in enumerate(B):
            for p in finds(x, a):
                for q in finds(y, b):
                    yield (unblocks(B[:i]+[(x[:p], y[:q])], S[:i]),
                           unblocks([(x[p+len(a):], y[q+len(b):])]+B[i+1:], S[i:]))
        return
    for i in range(len(S)-k+1):
        if S[i:i+k] != T or B[i+1:i+k] != A[1:k]: continue
        (a0,b0) = A[0]; (ak,bk) = A[k]; (x,y) = B[i]; (xk,yk) = B[i+k]
        if not (x.endswith(a0) and y.endswith(b0) and xk.startswith(ak) and yk.startswith(bk)): continue
        yield (unblocks(B[:i]+[(x[:len(x)-len(a0)], y[:len(y)-len(b0)])], S[:i]),
               unblocks([(xk[len(ak):], yk[len(bk):])]+B[i+k+1:], S[i+k:]))

class Lib:
    def __init__(self):
        self.rules = []   # (name, lhs, rhs) canonical
        self.proofs = {}  # name -> (lhs, rhs, steps)
    def add(self, name, l, r, steps=None):
        assert eq(l, r), name
        self.rules.append((name, canon(l), canon(r)))
        self.proofs[name] = (l, r, steps)
    def idx(self, name):
        for i,(n,_,_) in enumerate(self.rules):
            if n == name: return i
        raise KeyError(name)

def neighbors(w, rules, maxlen, maxins, allowed=None):
    for k,(name,l,r) in enumerate(rules):
        if allowed is not None and name not in allowed: continue
        for d,(a,b) in ((0,(l,r)),(1,(r,l))):
            if len(w)-len(a)+len(b) > maxlen: continue
            if a == '':
                if len(b) > maxins: continue
                seen = set()
                for p in range(len(w)+1):
                    v = canon(w[:p]+b+w[p:])
                    if v in seen: continue
                    seen.add(v); yield v, (w[:p], w[p:], k, d)
                continue
            for u, v in matches(w, a):
                yield canon(u+b+v), (u, v, k, d)

def search(src, dst, lib, maxlen=None, limit=300000, maxins=2, slack=4, allowed=None):
    rules = lib.rules
    src = canon(src); dst = canon(dst)
    if src == dst: return []
    if maxlen is None: maxlen = max(len(src), len(dst)) + slack
    fa = {src: None}; fb = {dst: None}
    qa = collections.deque([src]); qb = collections.deque([dst]); n = 0
    while qa and qb:
        if len(qa) <= len(qb): q, f, g = qa, fa, fb
        else: q, f, g = qb, fb, fa
        for _ in range(len(q)):
            w = q.popleft()
            for v, st in neighbors(w, rules, maxlen, maxins, allowed):
                if v in f: continue
                f[v] = (w, st); n += 1
                if v in g: return build(v, fa, fb)
                if n > limit: return None
                q.append(v)
    return None
def build(m, fa, fb):
    left = []; w = m
    while fa[w] is not None:
        p, st = fa[w]; left.append(st); w = p
    left.reverse()
    right = []; w = m
    while fb[w] is not None:
        p, (u, v, k, d) = fb[w]; right.append((u, v, k, 1-d)); w = p
    return left + right
def run(src, rules, steps):
    cur = canon(src)
    for (u, v, k, d) in steps:
        _, l, r = rules[k]; a, b = (l, r) if d == 0 else (r, l)
        assert canon(u+a+v) == cur
        cur = canon(u+b+v)
    return cur

SIG = {'h':'H','H':'h','z':'Z','Z':'z','C':'C','K':'SKS','S':'S'}
def sig(w): return ''.join(SIG[c] for c in w)
def rev(w): return w[::-1]
def add_variants(lib, name, l, r, steps):
    """add a lemma and its mirrored (rev), upside-down (sig) and both variants"""
    lib.add(name, l, r, steps)
    seen = {(canon(l), canon(r)), (canon(r), canon(l))}
    for tag, f in (('r', rev), ('s', sig), ('rs', lambda w: rev(sig(w)))):
        a, b = canon(f(l)), canon(f(r))
        if (a, b) in seen: continue
        seen.add((a, b)); seen.add((b, a))
        lib.add(name + tag, a, b, (tag, name))
