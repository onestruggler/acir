"""Cliff₃: the qutrit Clifford rule set, for the derivation machinery of
frag.py.  The gates are ω₁₂ (w), H (the Fourier matrix), S =
diag(1, 1, ω₃) and the qutrit CNOT |b₀ , b₁⟩ ↦ |b₀ + b₁ , b₁⟩ on a wire
and the one above it (CX10: control 1, target 0); circ reads them on
base-3 digits (DIM = 3, GATE_MATRIX).  Each axiom is spelled exactly as
Qutrit-Clifford.Kit lists it.  The shortcuts of Figure 9: K = H H,
H† = H H H, S† = S S, S′ = K S K, Z = S† S′, X = H Z H†."""
import cmath
import math
import re

import circ
import frag
from frag import (LIB, OUT, MIRROR, NATS, LABEL, CORE, SWAPS2, SWAPS3, NATLABELS,
                  MODULES, axiom, derive, add_mirror, placed, nat, outer, outer2, emit)

W3 = cmath.exp(2j * math.pi / 3)
ZETA = cmath.exp(1j * math.pi / 6)
R3 = 1 / math.sqrt(3)


def digit(x, w):
    return (x // 3 ** w) % 3


def setd(x, w, v):
    return x + (v - digit(x, w)) * 3 ** w


def gate_matrix(l, n):
    k, w = l
    N = 3 ** n
    M = [[0j] * N for _ in range(N)]
    for x in range(N):
        if k == 'w':
            M[x][x] = ZETA
        elif k == 'H':
            a = digit(x, w)
            for b in range(3):
                M[setd(x, w, b)][x] += R3 * W3 ** (a * b)
        elif k == 'S':
            M[x][x] = W3 if digit(x, w) == 2 else 1
        elif k == 'CX':
            b0, b1 = digit(x, w), digit(x, w + 1)
            M[setd(x, w, (b0 + b1) % 3)][x] = 1
        elif k == 'SW':
            b0, b1 = digit(x, w), digit(x, w + 1)
            M[setd(setd(x, w, b1), w + 1, b0)][x] = 1
        else:
            raise ValueError(l)
    return M


circ.DIM = 3
circ.GATE_MATRIX = gate_matrix
circ.GREEDY_SCALARS = True


def mac(rx, fn):
    circ.MACROS.append((re.compile(rx), fn))


def H(k): return [('H', k)]
def S(k): return [('S', k)]


def K(k): return H(k) * 2
def Hd(k): return H(k) * 3
def Sd(k): return S(k) * 2
def Sp(k): return K(k) + S(k) + K(k)
def Z(k): return Sd(k) + Sp(k)
def X(k): return H(k) + Z(k) + Hd(k)


mac(r'K(\d)', lambda m: K(int(m[1])))
mac(r'Hd(\d)', lambda m: Hd(int(m[1])))
mac(r'Sd(\d)', lambda m: Sd(int(m[1])))
mac(r'Sp(\d)', lambda m: Sp(int(m[1])))
mac(r'Z(\d)', lambda m: Z(int(m[1])))
mac(r'X(\d)', lambda m: X(int(m[1])))

axiom('ω¹²⁼', 0, 'w12', '')
axiom('H⁴⁼', 1, 'H0 H0 H0 H0', '')
axiom('S³⁼', 1, 'S0 S0 S0', '')
axiom('E⁼', 1, 'S0 H0 S0', 'H0 H0 H0 S0 S0 H0 H0 H0 w')
axiom('SS′⁼', 1, 'S0 K0 S0 K0', 'K0 S0 K0 S0')
axiom('CPh⁼', 2, 'CX10 S1 K0 CX10', 'S1 K0')
axiom('KC⁼', 2, 'K1 CX10', 'CX10 CX10 K1')
axiom('CZ⁼', 2, 'H0 CX10 Hd0', 'S1 S0 CX10 Sd0 CX10 CX10')
axiom('B⁼', 2, 'SW01 CX10', 'CX10 SW01 CX10 SW01 SW01 CX10 SW01 K1')
axiom('I⁼', 3, 'CX10 CX21 SW01 CX21 SW01', 'CX21 CX10')
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σS⁼', 2, 'S0 SW01', 'SW01 S1')
axiom('σCX⁼', 3, 'CX10 SW12 SW01', 'SW12 SW01 CX21')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

LABEL.update({'w12': 'ω¹²⁼', 'H4': 'H⁴⁼', 'S3': 'S³⁼', 'E': 'E⁼', 'SS′': 'SS′⁼', 'CPh': 'CPh⁼',
              'KC': 'KC⁼', 'CZ': 'CZ⁼', 'B': 'B⁼', 'I': 'I⁼',
              'ss': 'σσ⁼', 'sH': 'σH⁼', 'sS': 'σS⁼', 'sCX': 'σCX⁼', 'sss': 'σσσ⁼'})

CORE += ['H⁴⁼', 'S³⁼', 'ω¹²⁼', 'σσ⁼']
SWAPS2 += ['σH⁼', 'σS⁼']
SWAPS3 += ['σCX⁼', 'σσσ⁼']
NATLABELS += ['sH', 'sS', 'ss', 'sCX', 'sss']

frag.SELFINV.update({'SW'})

MODULES.update({'syntax': 'Examples.Independence.Qutrit-Clifford.Syntactics',
                'kit': 'Examples.Independence.Qutrit-Clifford.Kit',
                'kitname': 'Qutrit-Clifford.Kit'})


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    from circ import parse, same
    for name in ['ω¹²⁼', 'H⁴⁼', 'S³⁼', 'E⁼', 'SS′⁼', 'CPh⁼', 'KC⁼', 'CZ⁼', 'B⁼', 'I⁼',
                 'σσ⁼', 'σH⁼', 'σS⁼', 'σCX⁼', 'σσσ⁼']:
        e = LIB[name]
        print(name, same(e.lhs, e.rhs, max(e.arity, 1)))
