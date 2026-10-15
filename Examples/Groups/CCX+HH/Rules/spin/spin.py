"""Spin double-cover signs of circuit relations.

Every gate of X, CX, CCX, HH (and H) on n >= 4 wires is a rotation of
R^(2^n), so it lifts to the spin group.  A relation r (a word whose
matrix is I) lifts to +1 or -1 there; which one depends on the lifts
chosen for the gates only through how often each gate occurs.  This
module computes those lifts on the spinor space of Cl(2^n) (dimension
2^(2^(n-1))): feasible for n <= 5.

Gates are reflected as products of reflections in unit vectors; a
reflection in v lifts to the Clifford vector v (v^2 = |v|^2 = 1).
"""
import cmath, math, random, sys

class Spin:
    def __init__(self, n):
        self.n = n
        self.m = 2 ** n              # dimension of the rotated space
        assert self.m % 2 == 0
        self.k = self.m // 2         # spinor qubits
        self.dim = 2 ** self.k

    # gamma_mu applied to psi (Jordan-Wigner: gamma_{2j} = Z..Z X, gamma_{2j+1} = Z..Z Y)
    def gamma(self, mu, psi):
        j, odd = divmod(mu, 2)
        bit = 1 << j
        low = bit - 1
        out = [0j] * self.dim
        for idx, a in enumerate(psi):
            if a == 0:
                continue
            s = -1 if bin(idx & low).count('1') % 2 else 1
            tgt = idx ^ bit
            if odd:
                # Y|0> = i|1>, Y|1> = -i|0>
                ph = 1j if not (idx & bit) else -1j
                out[tgt] += s * ph * a
            else:
                out[tgt] += s * a
        return out

    def vec(self, v, psi):
        """Apply the Clifford vector sum_mu v[mu] gamma_mu (v a dict)."""
        out = [0j] * self.dim
        for mu, c in v.items():
            if c == 0:
                continue
            g = self.gamma(mu, psi)
            for i in range(self.dim):
                out[i] += c * g[i]
        return out

def transposition(a, b):
    r = 1 / math.sqrt(2)
    return {a: r, b: -r}

def bits(x, n):
    return [(x >> i) & 1 for i in range(n)]

# Gates as lists of reflection vectors (dicts index -> coefficient),
# in a fixed order: the lift is the product in this order.
def gate_reflections(g, n):
    kind = g[0]
    refl = []
    N = 2 ** n
    if kind in ('X', 'CX', 'CCX'):
        t = g[-1]
        ctrls = list(g[1:-1])
        for x in range(N):
            if (x >> t) & 1:
                continue
            if all((x >> c) & 1 for c in ctrls):
                refl.append(transposition(x, x | (1 << t)))
    elif kind == 'HH':
        s, t = g[1], g[2]
        # K = H(x)H on the block {x, x^s, x^t, x^s^t}; -1 eigenspace
        # spanned by (1,-1,-1,-1)/2 and (-1,-1,-1,1)/2? computed below
        for x in range(N):
            if (x >> s) & 1 or (x >> t) & 1:
                continue
            p00, p01, p10, p11 = x, x | (1 << t), x | (1 << s), x | (1 << s) | (1 << t)
            # basis order (s,t): 00,01,10,11 ; H(x)H entries (1/2)(-1)^{a.b}
            # -1 eigenvectors of H(x)H: (1,-1,-1,-1)/2 and  (−1,−1,−1,1)? check: use
            # v1=(1,-1,-1,-1)/2, v2 orthogonal in -1 space: (0,1,-1,0)/sqrt2
            v1 = {p00: 0.5, p01: -0.5, p10: -0.5, p11: -0.5}
            r = 1 / math.sqrt(2)
            v2 = {p01: r, p10: -r}
            refl.append(v1)
            refl.append(v2)
    elif kind == 'H':
        t = g[1]
        # H on wire t: reflection in (sin(pi/8)?)  H = reflection in v=(1,-1)/sqrt? ;
        # H has eigenvalues +1,-1; -1 eigenvector (sin(pi/8), -cos(pi/8))
        a, b = math.sin(math.pi / 8), -math.cos(math.pi / 8)
        for x in range(N):
            if (x >> t) & 1:
                continue
            refl.append({x: a, x | (1 << t): b})
    else:
        raise ValueError(g)
    return refl

def apply_gate(S, g, psi, cache={}):
    key = (S.n, g)
    if key not in cache:
        cache[key] = gate_reflections(g, S.n)
    for v in cache[key]:
        psi = S.vec(v, psi)
    return psi

def lift_sign(n, word, seed=1):
    """Sign of the lifted relation (word in time order; its matrix must be I)."""
    S = Spin(n)
    rnd = random.Random(seed)
    psi0 = [complex(rnd.gauss(0, 1), rnd.gauss(0, 1)) for _ in range(S.dim)]
    psi = psi0
    for g in word:
        psi = apply_gate(S, g, psi)
    # psi should be +-psi0
    num = sum(a.conjugate() * b for a, b in zip(psi0, psi))
    den = sum(abs(a) ** 2 for a in psi0)
    ratio = num / den
    return ratio

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    for g in [('X', 0), ('CX', 1, 0), ('CCX', 2, 1, 0), ('HH', 0, 1), ('H', 0)]:
        print(g, 'square ->', lift_sign(n, [g, g]))
