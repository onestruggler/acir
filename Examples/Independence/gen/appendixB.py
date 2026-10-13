"""Appendix B of Blake's paper: auxiliary derivations for RCliff₂.

As appendixA.py: the paper's chains, one line per string, in time
order (wire 0 at the bottom of the figures), Z a gate of its own.  The
paper's figures B.1–B.10 are transcribed; the lemmas after them (the
CNOT calculus of Appendix A in RCliff₂: A.8c, A.13–A.15, and the
commutations of a CZ with a CNOT sharing its control) are what the
decodings of (R13)–(R16) need, which the paper leaves to be mimicked
from the Clifford ones."""
import rcliff
from frag import derive, add_mirror, placed, nat, LIB, OUT
import frag


def D(name, width, lines, **kw):
    derive(name, width, lines, **kw)


# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σZ′⁼', 2, [('SW01 Z0', None), ('Z1 SW01', ['sZ', 'ss'])])
for n in ['CX²⁼', 'B⁼', 'ZC⁼', 'CZr⁼', 'CF⁼']:
    add_mirror(n)

# B.1: CZ is symmetric.
D('B1⁼', 2, [('H0 CX10 H0', None), ('H1 CX01 H1', ['H2', 'CZr'])])

# B.2: (R4).
D('B2⁼', 1, [('Z0 H0 Z0 H0 Z0 H0 Z0 H0', None),
             ('m H0 Z0 H0 Z0 Z0 H0 Z0 H0', ['F']),
             ('m', ['H2', 'Z2'])])

# B.3: (R5).
D('B3⁼', 2, [('H0 CX10 H0 H0 CX10 H0', None),
             ('H0 CX10 CX10 H0', ['H2']),
             ('H0 H0', ['CX2']),
             ('', ['H2'])])

# Z on the control passes the CNOT (the step of B.4 the paper draws in
# three lines).
D('ZC1⁼', 2, [('Z1 CX10', None), ('CX10 Z1', ['ZC', 'CX2', 'Z2'])], depth=8)

# B.4: (R6).
D('B4⁼', 2, [('Z1 H0 CX10 H0', None), ('H0 CX10 H0 Z1', ['ZC1⁼'])])

# B.5: (R7).
D('B5⁼', 2, [('Z0 H0 CX10 H0', None),
             ('Z0 H1 CX01 H1', ['B1⁼']),
             ('H1 CX01 H1 Z0', ['B4⁼']),
             ('H0 CX10 H0 Z0', ['B1⁼'])])

# B.6: (R8).
D('B6⁼', 2, [('H1 Z1 H1 H0 CX10 H0', None),
             ('H1 Z1 CX01 H1', ['H2', 'CZr']),
             ('H1 Z1 CX01 Z1 Z1 H1', ['Z2']),
             ('H1 CX01 Z1 H1 Z0', ['ZC']),
             ('H0 CX10 H0 H1 Z1 H1 Z0', ['H2', 'CZr'])])

# B.7: (R9), the mirror of B.6 between two B.1s.
D('B7⁼', 2, [('H0 Z0 H0 H0 CX10 H0', None),
             ('H0 Z0 H0 H1 CX01 H1', ['B1⁼']),
             ('H1 CX01 H1 H0 Z0 H0 Z1', ['B6⁼']),
             ('H0 CX10 H0 H0 Z0 H0 Z1', ['B1⁼'])])

# B.8: (R10).
D('B8⁼', 2, [('H1 H0 CX10 H1 H0 H0 CX10 H0', None),
             ('H1 H0 CX10 H0 CX01 H1', ['H2', 'CZr']),
             ('H1 H0 CX10 H0 Z0 Z0 CX01 H1', ['Z2']),
             ('H1 Z1 H0 CX10 H0 CX01 Z1 H1 Z0', ['ZC', 'B4⁼']),
             ('H1 Z1 H1 CX01 H1 CX01 Z1 H1 Z0', ['H2', 'CZr']),
             ('H1 Z1 H1 H1 Z1 CX01 H1 CX01 Z0', ['CF']),
             ('H1 CX01 H1 CX01 Z0', ['H2', 'Z2']),
             ('H0 CX10 H0 H1 H0 CX10 H0 H1 Z0', ['H2', 'CZr'])])

# B.9: (R11), the mirror of B.8 between B.1s.
D('B9⁼', 2, [('H0 H0 CX10 H0 H0 H0 CX10 H0', None),
             ('H0 H1 CX01 H1 H0 H1 CX01 H1', ['B1⁼']),
             ('H1 CX01 H1 H0 H1 CX01 H1 H0 Z1', ['B8⁼']),
             ('H0 CX10 H0 H0 H0 CX10 H0 H0 Z1', ['B1⁼'])])

# B.10: (R12).
D('B10⁼', 2, [('H0 H0 CX10 H0 H0 H0 H1 CX10 H0 H0 H0 H1 CX10 H0', None),
              ('CX10 H1 H0 CX10 H1 H0 CX10 H0', ['H2']),
              ('CX10 CX01 CX10 H0', ['CZr']),
              ('SW01 CX10 CX10 H0', ['B']),
              ('SW01 H0', ['CX2']),
              ('H0 SW01 H1 H0', ['H2']),
              ('H0 CX10 CX01 CX10 H1 H0', ['B', 'CX2']),
              ('H0 CX10 H1 H0 CX10 H1 H0 CX10 H1 H0', ['CZr']),
              ('H0 CX10 H0 H0 H1 H0 CX10 H0 H0 H1 H0 CX10 H0 H1', ['H2'])])

# ---------------------------------------------------------------------
# Appendix A's CNOT calculus, in RCliff₂

# H on a control.
D('A8c⁼', 2, [('H1 CX10 H1', None), ('H0 CX01 H0', ['CZr', 'H2'])])

# A gate on the middle wire passes a CNOT between the outer two.
D('MH⁼', 3, [('H1 CX20', None), ('CX20 H1', ['sH'])])
D('MZ⁼', 3, [('Z1 CX20', None), ('CX20 Z1', ['sZ'])])
D('MHᵘ⁼', 3, [('H1 CX02', None), ('CX02 H1', ['sH', 'sCX', 'sss'])])
D('MZᵘ⁼', 3, [('Z1 CX02', None), ('CX02 Z1', ['sZ', 'sCX', 'sss'])])
frag.SWAPS3 += ['MH⁼', 'MZ⁼', 'MHᵘ⁼', 'MZᵘ⁼']

# A.13: a CNOT across a wire, as a commutator.
D('A13⁼', 3, [('CX20 CX10', None),
              ('CX21 CX10 CX10 CX21 CX20 CX10', ['CX2']),
              ('CX21 CX10 CX21 CX10 CX10', ['I']),
              ('CX21 CX10 CX21', ['CX2'])])

# A.14: a common target.
D('A14⁼', 3, [('CX20 CX10', None),
              ('CX20 CX10 CX20 CX10 CX10 CX20', ['CX2']),
              ('CX21 CX10 CX21 CX21 CX10 CX21 CX10 CX20', ['A13⁼']),
              ('CX10 CX20', ['CX2'])])

# A.15: a common control.
D('A15⁼', 3, [('CX20 CX21', None),
              ('H2 H1 H0 CX02 CX12 H2 H1 H0', ['CZr', 'H2']),
              ('H2 H1 H0 CX12 CX02 H2 H1 H0', [placed('A14⁼', [0, 1, 0])]),
              ('CX21 CX20', ['CZr', 'H2'])])

# CNOTs with the control on wire 1 commute.
CC = placed('A15⁼', [1])                # CX10 CX12 = CX12 CX10
CT = placed('A14⁼', [0])                # CX21 CX01 = CX01 CX21

# A CZ passes a CNOT that shares its control.
D('K1⁼', 3, [('CX10 H1 CX21 H1', None),
             ('CX10 H2 CX12 H2', ['B1⁼']),
             ('H2 CX12 CX10 H2', [CC]),
             ('H1 CX21 H1 CX10', ['B1⁼'])])
D('K2⁼', 3, [('CX12 H0 CX10 H0', None), ('H0 CX10 H0 CX12', [CC])])
