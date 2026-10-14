"""RCliff₂'s auxiliary derivations, and Makary, Ross and Selinger's
relations decoded and derived in RCliff₂ (the paper's Appendix D.2 and
G.2).  Each derivation is a chain of circuits in time order, in the
notation of circ.gparse with Z a gate of its own (rcliff.py); the
labels name the equations of each step.

Run through mkmod.py to write the Agda module."""
import rcliff
from rcliff import LIB, OUT, derive, add_mirror, placed, nat
from realstab import C, ARITY, D as decode, text

def D(name, width, lines, **kw):
    derive(name, width, lines, **kw)

# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σZ′⁼', 2, [('SW01 Z0', None), ('Z1 SW01', ['sZ', 'ss'])])
for n in ['B⁼', 'ZC⁼', 'CZr⁼', 'CF⁼']:
    add_mirror(n)

# H ⊗ H turns a CNOT upside down (A.8 of Cliff₂), and its corollaries:
# CZ is symmetric (A.9), H on a control (A.8c).
D('A8⁼', 2, [('CX10 H1 H0', None), ('H0 H1 CX01', ['CZr', 'H2'])])
D('A9⁼', 2, [('H0 CX10 H0', None), ('H1 CX01 H1', ['CZr', 'H2'])])
D('A8c⁼', 2, [('H1 CX10 H1', None), ('H0 CX01 H0', ['CZr', 'H2'])])

# Z on the control passes the CNOT.
D('ZCc⁼', 2, [('Z1 CX10', None), ('CX10 Z1', None)])

# A CNOT across a wire, as a commutator (A.13).
D('A13⁼', 3, [('CX20 CX10', None),
              ('CX21 CX10 CX10 CX21 CX20 CX10', ['CX2']),
              ('CX21 CX10 CX21 CX10 CX10', ['I']),
              ('CX21 CX10 CX21', ['CX2'])])

# A gate on the middle wire passes a CNOT between the outer two.
D('MH⁼', 3, [('H1 CX20', None), ('CX20 H1', ['sH'])])
D('MZ⁼', 3, [('Z1 CX20', None), ('CX20 Z1', ['sZ'])])
D('MHᵘ⁼', 3, [('H1 CX02', None), ('CX02 H1', ['sH', 'sCX', 'sss'])])
D('MZᵘ⁼', 3, [('Z1 CX02', None), ('CX02 Z1', ['sZ', 'sCX', 'sss'])])
import frag
frag.SWAPS3 += ['MH⁼', 'MZ⁼', 'MHᵘ⁼', 'MZᵘ⁼']

# Two CNOTs with a common target commute (A.14), and with a common
# control (A.15).
D('A14⁼', 3, [('CX20 CX10', None),
              ('CX20 CX10 CX20 CX10 CX10 CX20', ['CX2']),
              ('CX21 CX10 CX21 CX21 CX10 CX21 CX10 CX20', ['A13⁼']),
              ('CX10 CX20', ['CX2'])])
D('A15⁼', 3, [('CX20 CX21', None),
              ('H2 H1 H0 CX02 CX12 H2 H1 H0', ['A8⁼', 'H2']),
              ('H2 H1 H0 CX12 CX02 H2 H1 H0', [placed('A14⁼', [0, 1, 0])]),
              ('CX21 CX20', ['A8⁼', 'H2'])])

# The swap, from three CNOTs (A.16).
D('A16⁼', 2, [('SW01', None),
              ('SW01 CX10 CX10', ['CX2']),
              ('CX10 CX01 CX10', ['B'])])

NAME = {k: 'D' + k + '⁼' for k in C}

def direct(k, labels=None):
    l, r = C[k]
    D(NAME[k], ARITY[k], [(text(decode(l)), None), (text(decode(r)), labels)], mirror=False)

for k in ['R₁', 'R₂', 'R₃', 'R₄', 'R₅', 'R₆', 'R₇']:
    direct(k)

def L(k, side):
    return text(decode(C[k][side]))

# (R8): through the CNOT turned over, two Zs, and (ZC) mirrored.
D(NAME['R₈'], 2, [(L('R₈', 0), None),
                  ('H1 Z1 CX01 H1', ['A9⁼', 'H2']),
                  ('H1 Z1 CX01 Z1 Z1 H1', ['Z2']),
                  ('H1 CX01 Z1 Z0 H1', ['ZC']),
                  (L('R₈', 1), ['A9⁼', 'H2'])], mirror=False)

# (R9): the same on the target, where (ZC) applies as it stands.
D(NAME['R₉'], 2, [(L('R₉', 0), None),
                  ('H0 Z0 CX10 H0', ['H2']),
                  ('H0 Z0 CX10 Z0 Z0 H0', ['Z2']),
                  ('H0 CX10 Z1 Z0 H0', ['ZC']),
                  (L('R₉', 1), ['H2'])], mirror=False)

# (R10), the paper's chain.
D(NAME['R₁₀'], 2, [(L('R₁₀', 0), None),
                   ('H1 H0 CX10 H0 CX01 H1', ['A9⁼', 'H2']),
                   ('H1 H0 CX10 H0 Z0 Z0 CX01 H1', ['Z2']),
                   ('H1 H0 CX10 H0 Z1 Z0 CX01 Z1 H1', ['ZC', 'ZCc⁼']),
                   ('H1 Z1 H0 CX10 H0 CX01 Z1 H1 Z0', [NAME['R₆'], 'ZCc⁼']),
                   ('H1 Z1 H1 CX01 H1 CX01 Z1 H1 Z0', ['A9⁼', 'H2']),
                   ('H1 Z1 H1 H1 Z1 CX01 H1 CX01 Z0', ['CF']),
                   ('H1 CX01 H1 CX01 Z0', ['H2', 'Z2']),
                   (L('R₁₀', 1), ['A9⁼', 'H2'])], mirror=True)

# (R11): (R10) on the other wire, between turned-over CNOTs.
D(NAME['R₁₁'], 2, [(L('R₁₁', 0), None),
                   ('H0 H1 CX01 H1 H0 H1 CX01 H1', ['A9⁼']),
                   ('H1 CX01 H1 H0 H1 CX01 H1 H0 Z1', [NAME['R₁₀']]),
                   (L('R₁₁', 1), ['A9⁼'])], mirror=False)

# (R12), the paper's chain.
D(NAME['R₁₂'], 2, [(L('R₁₂', 0), None),
                   ('CX10 H1 H0 CX10 H1 H0 CX10 H0', ['H2']),
                   ('CX10 CX01 CX10 H0', ['CZr']),
                   ('SW01 CX10 CX10 H0', ['B']),
                   ('SW01 H0', ['CX2']),
                   ('SW01 H1 H1 H0', ['H2']),
                   ('H0 SW01 H1 H0', ['sH']),
                   ('H0 SW01 CX10 CX10 H1 H0', ['CX2']),
                   ('H0 CX10 CX01 CX10 H1 H0', ['B']),
                   ('H0 CX10 H1 H0 CX10 H1 H0 CX10 H1 H0', ['CZr']),
                   (L('R₁₂', 1), ['H2'])], mirror=False)

# (R13) is Cliff₂'s (C12), and (A.25)'s chain read backwards.
D(NAME['R₁₃'], 3, [(L('R₁₃', 0), None),
                   ('H1 CX21 CX01 H1 H0 H0', ['A8⁼']),
                   ('H0 H0 H1 CX21 CX01 H1', ['H2']),
                   ('H0 H0 H1 CX01 CX21 H1', [placed('A14⁼', [0])]),
                   (L('R₁₃', 1), ['A8⁼'])], mirror=False)

# (R14)–(R16).  The paper leaves them to be mimicked from Cliff₂'s (C13)–
# (C15): their relators are, inverse pairs cancelled, rotations of those
# of (C13)–(C15), decoded.  So first (C13)–(C15) decoded, by the chains
# of Cliff₂'s (A.26)–(A.28), which use no S; then each (Rj) from its
# (Ci) by inserting and cancelling inverse pairs (frag.relator_chain).
from frag import relator_chain, nat
from circ import permute
from selinger import C as SC, D as sdecode, text as stext

A14p = placed('A14⁼', [0])            # CX21 CX01 = CX01 CX21
n1 = nat(1, ('CX', 0, 1)).name         # SW12 CX01 = CX02 SW12

D('SC₁₃⁼', 3, [
  ('H1 CX21 H1 H2 H1 H1 CX21 H1 H1 H0 H0 CX10 H0 H1 H0 H1 CX21 H1 H2 H1 H1 CX21 H1', None),
  ('H1 CX21 H2 H1 CX21 CX10 CX21 H2 H1 CX21 H1', ['H2']),
  ('H1 CX21 CX12 H2 H1 CX10 H2 H1 CX12 CX21 H1', ['A8⁼', 'H2']),
  ('H1 CX21 CX12 H1 CX10 H1 CX12 CX21 H1', ['H2']),
  ('H1 CX21 CX12 H0 CX01 H0 CX12 CX21 H1', ['A8c⁼']),
  ('H1 SW12 CX21 H0 CX01 H0 CX21 SW12 H1', ['B']),
  ('H1 SW12 H0 CX01 H0 CX21 CX21 SW12 H1', [A14p]),
  ('H1 SW12 H0 CX01 H0 SW12 H1', ['CX2']),
  ('SW12 H0 CX01 H0 SW12', ['H2']),
  ('H0 CX02 H0', [n1]),
  ('H2 CX20 H2', ['A8c⁼']),
  ('H1 SW01 H2 CX21 H2 SW01 H1', ['H2']),
  ('H1 SW01 H2 CX21 H2 CX01 CX01 SW01 H1', ['CX2']),
  ('H1 SW01 CX01 H2 CX21 H2 CX01 SW01 H1', [A14p]),
  ('H1 CX01 CX10 H2 CX21 H2 CX10 CX01 H1', ['B']),
  ('H1 CX01 CX10 H0 H2 CX21 H2 H0 CX10 CX01 H1', ['H2']),
  ('H1 CX01 CX10 H1 H0 H1 H2 CX21 H2 H1 H1 H0 CX10 CX01 H1', ['H2']),
  ('H0 CX10 H0 H1 CX10 H1 H0 H1 H2 CX21 H2 H1 H1 H0 CX10 H1 H0 CX10 H0', ['A9⁼']),
  ('H0 CX10 H1 H0 CX10 H0 H1 H1 H2 CX21 H2 H1 H1 H0 CX10 H1 H0 CX10 H0', ['A8c⁼', 'A9⁼', 'H2']),
  ('H0 CX10 H0 H1 H0 H0 CX10 H0 H1 H1 H2 CX21 H2 H1 H1 H0 CX10 H0 H1 H0 H0 CX10 H0', ['H2']),
  ('H0 CX10 H0 H0 H1 H0 CX10 H0 H1 H2 H1 CX21 H1 H1 H2 H0 CX10 H0 H0 H1 H0 CX10 H0', ['H2'])],
  mirror=False)


def hcancel_steps(gs):
    """Delete pairs of H on one wire with nothing else on it between, one
    pair at a time: the circuits after each deletion."""
    from circ import gwires
    gs = list(gs)
    out = []
    changed = True
    while changed:
        changed = False
        for i, g in enumerate(gs):
            if g[0] != 'H':
                continue
            for j in range(i + 1, len(gs)):
                if g[1] in gwires(gs[j]):
                    if gs[j] == g:
                        del gs[j], gs[i]
                        out.append(list(gs))
                        changed = True
                    break
            if changed:
                break
    return out


c14 = sdecode(SC['C₁₄'][0])
D('SC₁₄⁼', 3, [
  (stext(c14), None)] + [(stext(c), ['H2']) for c in hcancel_steps(c14)] + [
  ('H2 CX12 CX21 H2 H0 CX10 H1 CX21 H2 H1 CX21 H2 CX10 H1 CX21 H2 H1 CX21 H2 CX10 H0', ['A8⁼', 'H2']),
  ('H2 CX12 CX21 H2 H0 CX10 H2 CX12 CX21 H2 CX10 H1 CX21 H2 H1 CX21 H2 CX10 H0', ['A8⁼', 'H2']),
  ('H2 CX12 CX21 H2 H0 CX10 H2 CX12 CX21 H2 CX10 H2 CX12 CX21 H2 CX10 H0', ['A8⁼', 'H2']),
  ('H2 CX12 CX21 H0 CX10 CX12 CX21 CX10 CX12 CX21 CX10 H2 H0', ['H2']),
  ('H2 CX21 SW12 H0 CX10 CX12 CX21 CX10 CX21 SW12 H2 CX10 H0', ['B']),
  ('H2 CX21 SW12 H0 CX10 CX12 CX20 CX10 SW12 H2 CX10 H0', ['A13⁼']),
  ('H2 CX21 H0 CX20 SW12 CX12 CX20 CX10 SW12 H2 CX10 H0', [nat(1, ('CX', 1, 0)).name]),
  ('H2 CX21 H0 CX20 CX21 SW12 CX20 CX10 SW12 H2 CX10 H0', [nat(1, ('CX', 1, 2)).name]),
  ('H2 CX21 H0 CX20 CX21 CX10 SW12 CX10 SW12 H2 CX10 H0', [nat(1, ('CX', 2, 0)).name]),
  ('H2 CX21 H0 CX20 CX21 CX10 CX20 SW12 SW12 H2 CX10 H0', [nat(1, ('CX', 1, 0)).name]),
  ('H2 CX21 H0 CX20 CX21 CX10 CX20 CX10 H2 H0', ['ss']),
  ('H2 H0 CX20 CX21 CX21 CX10 CX10 CX20 H2 H0', ['A14⁼', 'A15⁼']),
  ('H2 H0 H2 H0', ['CX2']),
  ('', ['H2'])], mirror=False)

# (C15) is (C14) with the wires reversed, each decoded CZ turned round
# by (A.9).
rev = lambda w: 2 - w
c15 = sdecode(SC['C₁₅'][0])
target = [permute(g, rev) for g in c14]
lines = [(stext(c15), None)]
cur = list(c15)
i = 0
while cur != target:
    while cur[i] == target[i]:
        i += 1
    h, x = cur[i], cur[i + 1]
    assert h[0] == 'H' and x[0] == 'CX' and cur[i + 2] == h, (i, cur[i:i + 3])
    c, t = x[1], x[2]
    cur = cur[:i] + [('H', c), ('CX', t, c), ('H', c)] + cur[i + 3:]
    lines.append((stext(cur), ['A9⁼']))
lines.append(('', [placed('SC₁₄⁼', [0, 1, 0])]))
D('SC₁₅⁼', 3, lines, mirror=False)

from circ import parse
PAIRS = ['H2', 'CX2', 'Z2', 'ss', 'm2']
for rk, ck in [('R₁₄', 'SC₁₃⁼'), ('R₁₅', 'SC₁₄⁼'), ('R₁₆', 'SC₁₅⁼')]:
    e = LIB[ck]
    D(NAME[rk], 3, relator_chain(parse(L(rk, 0)), parse(L(rk, 1)), e.lhs, e.rhs, ck, PAIRS),
      mirror=False)

# Lemma 19: the encodings of CNOT (H CZ H on the target) and of the swap
# (three such CNOTs), decoded.
D('DCX⁼', 2, [('H0 H0 CX10 H0 H0', None), ('CX10', ['H2'])], mirror=False)
D('Dσ⁼', 2, [('H0 H0 CX10 H0 H0 H1 H0 CX10 H0 H1 H0 H0 CX10 H0 H0', None),
             ('CX10 H1 H0 CX10 H0 H1 CX10', ['H2']),
             ('CX10 CX01 CX10', ['CZr']),
             ('SW01 CX10 CX10', ['B']),
             ('SW01', ['CX2'])], mirror=False)
