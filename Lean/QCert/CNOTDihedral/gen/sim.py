"""Phase-affine simulator for CNOT-dihedral circuits (numerical checks).

An operator on n wires is a pair (f, ph): f maps a state (tuple of bits,
wire 0 first) to a state, ph maps a state to Z/8 (the exponent of omega).
Composition is in operator order: a * b applies b first, as in the Lean
development (`PA`, `paQ`).
"""
import itertools


def states(n):
    return list(itertools.product((0, 1), repeat=n))


class Op:
    def __init__(self, n, f, ph):
        self.n = n
        self.f = f      # dict state -> state
        self.ph = ph    # dict state -> int mod 8

    def __mul__(self, other):
        assert self.n == other.n
        f = {}
        ph = {}
        for x in states(self.n):
            y = other.f[x]
            f[x] = self.f[y]
            ph[x] = (other.ph[x] + self.ph[y]) % 8
        return Op(self.n, f, ph)

    def __eq__(self, other):
        return self.n == other.n and self.f == other.f and self.ph == other.ph

    def inv(self):
        f = {}
        ph = {}
        for x in states(self.n):
            y = self.f[x]
            f[y] = x
            ph[y] = (-self.ph[x]) % 8
        return Op(self.n, f, ph)

    def __pow__(self, k):
        r = ident(self.n)
        for _ in range(k):
            r = r * self
        return r


def mkop(n, fun, phase=lambda x: 0):
    S = states(n)
    return Op(n, {x: tuple(fun(list(x))) for x in S}, {x: phase(list(x)) % 8 for x in S})


def ident(n):
    return mkop(n, lambda x: x)


def om(n):
    return mkop(n, lambda x: x, lambda x: 1)


def X(n, i):
    def f(x):
        x[i] ^= 1
        return x
    return mkop(n, f)


def T(n, i):
    return mkop(n, lambda x: x, lambda x: x[i])


def c(n, a, b):
    """CNOT with control a, target b (the Lean `cc a b`)"""
    def f(x):
        x[b] ^= x[a]
        return x
    return mkop(n, f)


def cx(n, i):
    """`qCX i`: control i + 1, target i"""
    return c(n, i + 1, i)


def sw(n, i):
    def f(x):
        x[i], x[i + 1] = x[i + 1], x[i]
        return x
    return mkop(n, f)


def shift(op):
    """op on n wires -> op on wires 1..n of n+1 wires"""
    n = op.n
    f = {}
    ph = {}
    for x in states(n + 1):
        f[x] = (x[0],) + op.f[x[1:]]
        ph[x] = op.ph[x[1:]]
    return Op(n + 1, f, ph)


def prod(ops, n):
    r = ident(n)
    for o in ops:
        r = r * o
    return r


def gadget(n, wires):
    """phase omega^(xor of the bits on `wires`)"""
    return mkop(n, lambda x: x, lambda x: sum(x[w] for w in wires) % 2)
