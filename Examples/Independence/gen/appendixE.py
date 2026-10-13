"""Appendix E of Blake's paper: auxiliary derivations for CliffCS₂.

As appendixA.py: the paper's chains, one line per string, in time
order, wire 0 at the bottom of the figures.  CS is a gate (CS01 on
wires 0 and 1, CS12, and CS02 between the outer wires, spelt with
swaps); CX10 is H0 CS01 CS01 H0, the CNOT the syntax defines (control
wire 1), and CX01 is H1 CS01 CS01 H1, its control on wire 0 — the
spelling the decoding of the source's CNOT produces, which DX relates
to the syntax's σ CX σ."""
import cliffCS
from frag import derive, add_mirror, placed, nat, LIB, OUT
import frag


def D(name, width, lines, **kw):
    derive(name, width, lines, **kw)


# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σS′⁼', 2, [('SW01 S0', None), ('S1 SW01', ['sS', 'ss'])])
D('σCS′⁼', 2, [('SW01 CS01', None), ('CS01 SW01', ['CSr', 'ss'])], mirror=False)
for n in ['CPh⁼', 'XCS⁼', 'CE⁼']:
    add_mirror(n)

# E.1: (S H)³ = ω.
D('E1⁼', 1, [('S0 H0 S0 H0 S0 H0', None),
             ('w S0 Sd0 H0 Sd0 S0 H0', ['E']),
             ('w H0 H0', ['S4']),
             ('w', ['H2'])])

# The CNOT with its control on wire 0, as the decoding spells it, is
# the syntax's CX under the swap; and the swap passes the CNOT.
D('DX⁼', 2, [('CX01', None),
             ('SW01 H0 SW01 CS01 CS01 SW01 H0 SW01', ['sH', 'σH′⁼', 'ss']),
             ('SW01 CX10 SW01', ['CSr', 'ss'])], mirror=False)
D('νCX⁼', 2, [('CX10 SW01', None), ('SW01 CX01', ['DX⁼', 'ss'])], mirror=False)
# B with the wires exchanged.
D('B↓⁼', 2, [('CX01 CX10', None),
             ('SW01 CX10 SW01 CX10', ['DX⁼']),
             ('SW01 CX10 SW01 CX10 SW01 SW01', ['ss']),
             ('SW01 SW01 CX10 SW01', ['B']),
             ('CX10 SW01', ['ss']),
             ('SW01 CX01', ['νCX⁼'])], mirror=False)
D('B′⁼', 2, [('CX10 CX01', None), ('CX10 SW01 CX10 SW01', ['DX⁼']),
             ('SW01 CX10', ['B'])], mirror=False)

# E.2: CS⁴ = ε.
D('E2⁼', 2, [('CS01 CS01 CS01 CS01', None),
             ('H0 H0 CS01 CS01 H0 H0 CS01 CS01 H0 H0', ['H2']),
             ('H0 CX10 CX10 H1 H1 S0 Sd0 H0', ['S4', 'H2']),
             ('H0 CX10 CX10 H1 CS01 CS01 S0 CS01 CS01 CS01 CS01 CS01 CS01 H1 Sd0 H0', ['CPh↓⁼']),
             ('H0 CX10 CX10 H1 CS01 CS01 S0 H1 H1 CS01 CS01 H1 H1 CS01 CS01 H1 H1 CS01 CS01 H1 '
              'Sd0 H0', ['H2']),
             ('H0 CX10 CX10 CX01 S0 CX01 CX01 CX01 Sd0 H0', []),
             ('H0 CX10 SW01 CX10 S0 CX01 CX01 CX01 Sd0 H0', ['B′⁼']),
             ('H0 SW01 CX01 CX10 S0 CX01 CX01 CX01 Sd0 H0', ['νCX⁼']),
             ('H0 SW01 SW01 CX01 S0 CX01 CX01 CX01 Sd0 H0', ['B↓⁼']),
             ('H0 CX01 S0 CX01 CX01 CX01 Sd0 H0', ['ss']),
             ('H1 H0 CS01 CS01 S0 CS01 CS01 CS01 CS01 CS01 CS01 H1 Sd0 H0', ['H2']),
             ('H1 H0 S0 H1 Sd0 H0', ['CPh↓⁼']),
             ('H1 H1 H0 H0', ['S4']),
             ('', ['H2'])], mirror=False)

# E.3, E.4: S on either wire passes CS.
D('E3⁼', 2, [('S1 CS01', None),
             ('CS01 S1 CS01 CS01 CS01 CS01', ['CPh']),
             ('CS01 S1', ['E2⁼'])], mirror=False)
D('E4⁼', 2, [('S0 CS01', None),
             ('CS01 S0 CS01 CS01 CS01 CS01', ['CPh↓⁼']),
             ('CS01 S0', ['E2⁼'])], mirror=False)

# E.5 is (XCS) with X spelt H Z H; E.6 and E.7 are (XCS) and (CE)
# mirrored, which derive adds.

# E.8: CS on the wires 0 1 and 1 2 commute.
D('E8⁼', 3, [('CS01 CS12', None),
             ('CS01 H1 H1 CS12 H1 H1', ['H2']),
             ('CS12 H1 H1 CS01 H1 H1', ['SH0']),
             ('CS12 CS01', ['H2'])])

# The CNOT is an involution, and the two spellings of CS02 agree.
D('CXCX⁼', 2, [('CX10 CX10', None), ('H0 CS01 CS01 CS01 CS01 H0', []),
               ('', ['E2⁼', 'H2'])], mirror=False)
D('CXCX↓⁼', 2, [('CX01 CX01', None), ('H1 CS01 CS01 CS01 CS01 H1', []),
                ('', ['E2⁼', 'H2'])], mirror=False)
D('CS02⁼', 3, [('SW12 CS01 SW12', None),
               ('SW12 CS01 SW12 SW01 SW01', ['ss']),
               ('SW12 SW12 SW01 CS12 SW01', ['sCS']),
               ('SW01 CS12 SW01', ['ss'])])

# E.9: (C13).
D('E9⁼', 3, [('CX12 CX21 CS01 CX21 CX12', None),
             ('SW12 CX12 CS01 CX12 SW12', ['B′⁼', 'B↓⁼', 'νCX⁼', 'B']),
             ('SW12 CX12 CX12 CS01 SW12', ['E8⁼']),
             ('SW12 H2 CS12 CS12 CS12 CS12 H2 CS01 SW12', ['H2']),
             ('SW12 H2 H2 CS01 SW12', ['E2⁼']),
             ('SW12 CS01 SW12', ['H2']),
             ('SW01 CS12 SW01', ['CS02⁼']),
             ('SW01 H0 H0 CS12 SW01', ['H2']),
             ('SW01 CS12 H0 CS01 CS01 CS01 CS01 H0 SW01', ['E2⁼']),
             ('SW01 H0 CS01 CS01 CS12 CS01 CS01 H0 SW01', ['E8⁼']),
             ('SW01 H0 CS01 CS01 H0 H0 CS12 H0 H0 CS01 CS01 H0 SW01', ['H2']),
             ('CX10 CX01 CS12 CX01 CX10', ['B′⁼', 'B↓⁼', 'νCX⁼', 'B'])])

# CS02 commutes with CS12 and with CS01.
D('E8b⁼', 3, [('CS12 SW01 CS12 SW01', None),
              ('CS12 SW12 CS01 SW12', ['CS02⁼']),
              ('SW12 CS12 CS01 SW12', ['σCS′⁼']),
              ('SW12 CS01 CS12 SW12', ['E8⁼']),
              ('SW12 CS01 SW12 CS12', ['σCS′⁼']),
              ('SW01 CS12 SW01 CS12', ['CS02⁼'])])
D('E8c⁼', 3, [('CS01 SW01 CS12 SW01', None),
              ('SW01 CS01 CS12 SW01', ['σCS′⁼']),
              ('SW01 CS12 CS01 SW01', ['E8⁼']),
              ('SW01 CS12 SW01 CS01', ['σCS′⁼'])])
# H on the middle wire passes CS02.
D('HCS02⁼', 3, [('H1 SW01 CS12 SW01', None), ('SW01 CS12 SW01 H1', ['sH', 'σH′⁼'])])
# Two CNOTs with the same control (wire 2) commute.
D('HCZ02⁼', 3, [('H1 SW01 CS12 CS12 SW01', None),
                ('SW01 CS12 CS12 SW01 H1', ['sH', 'σH′⁼'])])
D('CX2c⁼', 3, [('CX21 SW01 CX21 SW01', None),
               ('H1 CS12 CS12 H1 H0 SW01 CS12 CS12 SW01 H0', ['sH', 'σH′⁼']),
               ('H1 CS12 CS12 H0 SW01 CS12 CS12 SW01 H0 H1', ['HCZ02⁼']),
               ('H1 H0 SW01 CS12 CS12 SW01 H0 CS12 CS12 H1', ['E8b⁼']),
               ('H0 SW01 CS12 CS12 SW01 H0 H1 CS12 CS12 H1', ['HCZ02⁼']),
               ('SW01 CX21 SW01 CX21', ['sH', 'σH′⁼'])])
# The CNOT from wire 2 onto wire 1 carries CZ01 to CZ01 CZ02.
D('CZp⁼', 3, [('CX21 CS01 CS01 CX21', None),
              ('H0 CX21 CX10 CX21 H0', ['H2']),
              ('H0 CX10 CX21 SW01 CX21 SW01 CX21 H0', ['I']),
              ('H0 CX10 SW01 CX21 SW01 CX21 CX21 H0', ['CX2c⁼']),
              ('H0 CX10 SW01 CX21 SW01 H0', ['CXCX⁼']),
              ('CS01 CS01 SW01 CS12 CS12 SW01', ['H2', 'sH', 'σH′⁼'])])

# Two CNOTs with the same target (wire 1) commute.
D('CXt⁼', 3, [('CX21 CX01', None), ('H1 CS12 CS12 CS01 CS01 H1', ['H2']),
              ('H1 CS01 CS01 CS12 CS12 H1', ['E8⁼']), ('CX01 CX21', ['H2'])])

# CS02 passes the CNOT from wire 0 onto wire 1; CZp reflected (the
# CNOT from wire 0 onto wire 1 carries CZ12 to CZ12 CZ02); and so that
# CNOT conjugates CS12³ to something CZ12 passes.
D('CS02X⁼', 3, [('CS02 CX01', None),
                ('H1 CS02 CS01 CS01 H1', ['HCS02⁼']),
                ('H1 CS01 CS01 CS02 H1', ['E8c⁼']),
                ('CX01 CS02', ['HCS02⁼'])])
D('E8cz⁼', 3, [('CS01 CS02 CS02', None), ('CS02 CS02 CS01', ['E8c⁼'])])
D('E8z⁼', 3, [('CS02 CS02 CS12', None), ('CS12 CS02 CS02', ['E8b⁼'])])
CZPR = placed('CZp⁼', [0, 1, 0])
D('CZq⁼', 3, [('CS12 CS12 CS02 CS02 CX01', None),
              ('CS12 CS12 SW12 CS01 CS01 SW12 CX01', ['CS02⁼', 'ss']),
              ('CX01 CS12 CS12 CX01 CX01', [CZPR]),
              ('CX01 CS12 CS12', ['CXCX↓⁼'])])
D('CZq′⁼', 3, [('CX01 CS12 CS12 CS02 CS02', None),
               ('CX01 CS12 CS12 CS02 CS02 CX01 CX01', ['CXCX↓⁼']),
               ('CX01 CS12 CS12 CX01 CS02 CS02 CX01', ['CS02X⁼']),
               ('CS12 CS12 SW12 CS01 CS01 SW12 CS02 CS02 CX01', [CZPR]),
               ('CS12 CS12 SW12 CS01 CS01 CS01 CS01 SW12 CX01', ['CS02⁼', 'ss']),
               ('CS12 CS12 CX01', ['E2⁼', 'ss'])])
D('YZ⁼', 3, [('CX01 CS12 CS12 CS12 CX01 CS12 CS12', None),
             ('CX01 CS12 CS12 CS12 CS12 CS12 CS02 CS02 CX01', ['CZq⁼']),
             ('CX01 CS12 CS12 CS02 CS02 CS12 CS12 CS12 CX01', ['E8z⁼']),
             ('CS12 CS12 CX01 CS12 CS12 CS12 CX01', ['CZq′⁼'])])

# E.10: (C14).
D('E10⁼', 3, [('CS01 CX21 CS01 CS01 CS01 CX21', None),
              ('CS01 CS01 CS01 CS02 CS02 CX21 CS01 CX21', ['CZp⁼', 'CXCX⁼', 'E8c⁼']),
              ('CS01 CS01 CS01 CS02 CS02 CS12 CS12 CS12 CS12 CX21 CS01 CX21', ['E2⁼']),
              ('CS01 CS01 CS01 CS02 CS02 CS12 CS12 CS12 CS12 CX21 CS01 CX01 CX01 CX21',
               ['CXCX↓⁼']),
              ('CS01 CS01 CS01 CS02 CS02 CS12 CS12 CS12 CS01 CX01 CS12 CX21 CX01 CX21', ['SH2']),
              ('CS01 CS01 CS01 CS02 CS02 CS01 CS12 CS12 CS12 CX01 CS12 CX21 CX01 CX21', ['E8⁼']),
              ('CS01 CS01 CS01 CS01 CS02 CS02 CS12 CS12 CS12 CX01 CS12 CX21 CX01 CX21', ['E8c⁼']),
              ('CS02 CS02 CS12 CS12 CS12 CX01 CS12 CX21 CX01 CX21', ['E2⁼']),
              ('CS02 CS02 CS12 CS12 CS12 CX01 CS12 CX01', ['CXt⁼', 'CXCX⁼']),
              ('CS12 CS12 CS12 CS02 CS02 CX01 CS12 CX01', ['E8z⁼']),
              ('CS12 CS12 CS12 CX01 CS02 CS02 CS12 CX01', ['CS02X⁼']),
              ('CS12 CS12 CS12 CX01 CS12 CS02 CS02 CX01', ['E8z⁼']),
              ('CS12 CS12 CS12 CX01 CS12 CS12 CS12 CS12 CS12 CS02 CS02 CX01', ['E2⁼']),
              ('CS12 CS12 CS12 CX01 CS12 CS12 CS12 CX01 CS12 CS12', ['CZq⁼']),
              ('CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CS12 CX01', ['YZ⁼']),
              ('CS12 CX01 CS12 CS12 CS12 CX01', ['E2⁼'])])

# E.11: (C15), by E.9's first steps and CZp.
D('E11⁼', 3, [('CX12 CX21 CS01 CS01 CX21 CX12', None),
              ('SW12 CX12 CS01 CS01 CX12 SW12', ['B′⁼', 'B↓⁼', 'νCX⁼', 'B']),
              ('SW12 CX12 CX12 CS01 CS01 SW12', ['E8⁼']),
              ('SW12 CS01 CS01 SW12', ['CXCX↓⁼']),
              ('SW01 CS12 CS12 SW01', ['CS02⁼', 'ss']),
              ('CS01 CS01 CS01 CS01 SW01 CS12 CS12 SW01', ['E2⁼']),
              ('CS01 CS01 SW01 CS12 CS12 SW01 CS01 CS01', ['E8cz⁼']),
              ('CX21 CS01 CS01 CX21 CS01 CS01', ['CZp⁼'])])

# E.12: (C17).
D('E12⁼', 3, [('CS01 H1 CS01 CS01 CS01 H1 CS12 H1 CS01', None),
              ('CS01 H1 CS01 CS01 CS01 H1 CS12 H1 CS12 CS12 CS12 CS12 CS01', ['E2⁼']),
              ('CS12 H1 CS12 CS12 CS12 H1 CS01 H1 CS01 CS01 CS01 CS12 CS01', ['SH3']),
              ('CS12 H1 CS12 CS12 CS12 H1 CS01 H1 CS12', ['E8⁼', 'E2⁼'])])

# E.13: the swap.
D('E13⁼', 2, [('SW01', None),
              ('H1 SW01 H0 CS01 CS01 H0 H0 CS01 CS01 H0 H0', ['H2', 'E2⁼', 'sH', 'σH′⁼']),
              ('H1 CX10 CX01 CX10 H0', ['B′⁼']),
              ('H0 H1 CS01 CS01 H0 H1 CS01 CS01 H0 H1 CS01 CS01', ['H2'])], mirror=False)
