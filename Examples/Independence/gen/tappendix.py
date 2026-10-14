"""CliffT₂'s auxiliary derivations, and Bian and Selinger's relations
decoded and derived in CliffT₂ on two wires (the paper's Appendix D.3
and G.4).  Lines are in the notation of circ.gparse with tcliff's
spellings (S is T T); the labels name each step's equations.

Run through mkmod.py to write the Agda module."""
import sys
import tcliff
from tcliff import LIB, OUT, derive, add_mirror, placed, nat
import frag
from bst import C as BS, D as bdecode


def D(name, width, lines, **kw):
    derive(name, width, lines, **kw)


# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σT′⁼', 2, [('SW01 T0', None), ('T1 SW01', ['sT', 'ss'])])
for n in ['CPh⁼', 'B⁼', 'CZ⁼']:
    add_mirror(n)

# CNOT is an involution (the paper's t-CX2; Cliff₂'s A.5 with T).
D('A5⁼', 2, [('CX10 CX10', None),
             ('CX10 CX10 T0 Td0', ['T8']),
             ('CX10 CX10 CX01 T0 CX01 Td0', ['Ct']),
             ('CX10 SW01 CX10 T0 CX01 Td0', ['B']),
             ('CX10 CX01 SW01 T0 CX01 Td0', []),
             ('SW01 CX10 SW01 T0 CX01 Td0', ['B']),
             ('T0 Td0', ['Ct']),
             ('', ['T8'])])
frag.CORE.append('A5⁼')

# S on the control passes the CNOT (Cliff₂'s axiom CPh).
D('CPhS⁼', 2, [('CX10 S1 CX10', None),
               ('CX10 T1 CX10 CX10 T1 CX10', ['A5⁼']),
               ('S1', ['Ct'])])
frag.LABEL['CPh'] = 'CPhS⁼'

# Cliff₂'s two-wire chains (appendixA.py), as they stand: S is T T here,
# and the label CPh is the derived CPhS.
# A.1–A.4: one wire.
D('A1⁼', 1, [('Z0 Z0', None), ('', ['S4'])])
D('A2⁼', 1, [('X0 X0', None), ('H0 Z0 Z0 H0', ['H2']), ('H0 H0', ['A1⁼']), ('', ['H2'])])
# (A.3) and (A.3′) through the axiom TX: X conjugates T to ω T†.
D('XTX⁼', 1, [('X0 T0 X0', None), ('w Td0 X0 X0', ['TX']), ('w Td0', ['A2⁼'])])
D('XTdX⁼', 1, [('X0 Td0 X0', None),
               ('w8 X0 Td0 X0', ['w8']),
               ('w7 X0 X0 T0', ['TX']),
               ('w7 T0', ['A2⁼'])])
D('A3⁼', 1, [('X0 S0 X0', None),
             ('X0 T0 X0 X0 T0 X0', ['A2⁼']),
             ('w Td0 w Td0', ['XTX⁼']),
             ('w2 Sd0', ['T8'])])
D('A3d⁼', 1, [('X0 Sd0 X0', None),
              ('X0 Td0 Td0 X0', ['T8']),
              ('X0 Td0 X0 X0 Td0 X0', ['A2⁼']),
              ('w7 T0 w7 T0', ['XTdX⁼']),
              ('w6 S0', ['w8'])])
D('A4⁼', 1, [('H0', None), ('H0 Sd0 S0', ['S4']), ('H0 Sd0 H0 H0 S0', ['H2']),
             ('wd S0 H0 S0 H0 S0', ['E'])])

# A.6: S on the control passes the CNOT.
D('A6⁼', 2, [('S1 CX10', None), ('CX10 S1 CX10 CX10', ['CPh']), ('CX10 S1', ['A5⁼'])])

D('A6d⁼', 2, [('Sd1 CX10', None), ('CX10 Sd1', ['A6⁼'])])

# A.7: S on the target, between two CNOTs.
D('A7⁼', 2, [('CX10 S0 CX10', None),
             ('SW01 CX01 S1 CX01 SW01', []),
             ('CX01 CX10 S1 CX10 CX01', ['B']),
             ('CX01 S1 CX10 CX10 CX01', ['A6⁼']),
             ('CX01 S1 CX01', ['A5⁼'])])
# ... and with S† (A.7 three times).
D('A7d⁼', 2, [('CX10 Sd0 CX10', None),
              ('CX10 S0 CX10 CX10 S0 CX10 CX10 S0 CX10', ['A5⁼']),
              ('CX01 S1 CX01 CX01 S1 CX01 CX01 S1 CX01', ['A7⁼']),
              ('CX01 Sd1 CX01', ['A5⁼'])])

# A.8: H ⊗ H turns a CNOT upside down.
D('A8⁼', 2, [('CX10 H1 H0', None),
             ('H0 H0 CX10 H1 H0', ['H2']),
             ('H0 S1 S0 CX10 Sd0 CX10 H1', ['CZ']),
             ('H0 S1 S0 CX01 Sd1 CX01 H1', ['A7d⁼']),
             ('H0 H1 CX01 H1 H1', ['CZ']),
             ('H0 H1 CX01', ['H2'])])

# A.9: CZ is symmetric (a route through A.7 rather than the paper's).
D('A9⁼', 2, [('H0 CX10 H0', None),
             ('S1 S0 CX10 Sd0 CX10', ['CZ']),
             ('S1 S0 CX01 Sd1 CX01', ['A7d⁼']),
             ('H1 CX01 H1', ['CZ'])])

# A.10: X on the target passes the CNOT.
D('A10⁼', 2, [('X0 CX10', None),
              ('H0 S0 S0 H0 H1 H1 CX10', ['H2']),
              ('H0 S0 S0 H1 CX01 H1 H0', ['A8⁼', 'A9⁼']),
              ('H0 H1 CX01 H1 S0 S0 H0', ['A6⁼']),
              ('CX10 H1 H1 H0 S0 S0 H0', ['A8⁼', 'A9⁼']),
              ('CX10 X0', ['H2'])])

# A.11: X on the target is X on the control around the CNOT.
D('A11⁼', 2, [('CX10 X0', None),
              ('H0 H0 CX10 H0 H0 X0', ['H2']),
              ('H0 S1 S0 CX10 Sd0 CX10 H0 X0', ['CZ']),
              ('H0 S1 S0 CX01 Sd1 CX01 H0 X0', ['A7d⁼']),
              ('H0 S1 S0 CX01 Sd1 CX01 Z0 H0', ['H2']),
              ('H0 S1 S0 Z0 CX01 Sd1 CX01 H0', ['A6⁼']),
              ('H0 S1 Sd0 CX01 Sd1 CX01 H0', ['S4']),
              ('w6 H0 S1 Sd0 CX01 X1 S1 X1 CX01 H0', ['w8', 'A3⁼']),
              ('w8 H0 Sd0 X1 Sd1 X1 CX01 X1 S1 X1 CX01 H0', ['w8', 'A3d⁼']),
              ('H0 Sd0 X1 Sd1 X1 CX01 X1 S1 X1 CX01 H0', ['w8']),
              ('X1 Sd1 H0 Sd0 CX01 S1 X1 CX01 H0', ['A10⁼', 'A2⁼']),
              ('X1 Sd1 H0 Sd0 CX01 S1 CX01 X1 H0', ['A10⁼']),
              ('X1 Sd1 H0 Sd0 CX10 S0 CX10 X1 H0', ['A7⁼']),
              ('X1 Sd1 H0 CX10 CX10 Sd0 CX10 S0 CX10 X1 H0', ['A5⁼']),
              ('X1 H0 CX10 Sd1 CX10 Sd0 CX10 S0 CX10 X1 H0', ['A6d⁼']),
              ('X1 H0 CX10 Sd1 CX01 Sd1 CX01 S0 CX10 X1 H0', ['A7d⁼']),
              ('X1 H0 CX10 Sd1 S0 CX01 Sd1 CX01 CX10 X1 H0', ['A6⁼']),
              ('X1 H0 CX10 Sd1 S0 CX10 Sd0 CX10 CX10 X1 H0', ['A7d⁼']),
              ('X1 H0 CX10 Z1 H0 CX10 H0 CX10 X1 H0', ['CZ', 'S4']),
              ('X1 S1 S0 CX10 Sd0 CX10 Z1 CX10 S1 S0 CX10 Sd0 CX10 X1', ['CZ']),
              ('X1 S0 CX10 Sd0 CX10 CX10 S0 CX10 Sd0 CX10 X1', ['A6⁼', 'S4']),
              ('X1 S0 CX10 Sd0 S0 CX10 Sd0 CX10 X1', ['A5⁼']),
              ('X1 S0 Sd0 CX10 X1', ['S4', 'A5⁼']),
              ('X1 CX10 X1', ['S4'])])

# A.12: Z on the control is Z on the target around the CNOT.
D('A12⁼', 2, [('CX10 Z1', None),
              ('H1 H0 CX01 H1 H0 Z1', ['A8⁼']),
              ('H1 H0 CX01 X1 H1 H0', ['H2']),
              ('H1 H0 X0 CX01 X0 H1 H0', ['A11⁼']),
              ('Z0 H1 H0 CX01 H1 H0 Z0', ['H2']),
              ('Z0 CX10 Z0', ['A8⁼'])])

# A.16: the swap, from three CNOTs.
D('A16⁼', 2, [('SW01', None),
              ('H1 SW01 H0', ['H2']),
              ('H1 SW01 CX10 CX10 H0', ['A5⁼']),
              ('H1 CX10 CX01 CX10 H0', ['B']),
              ('H0 H0 H1 CX10 H0 H1 H0 H1 CX01 H0 H1 H0 H1 CX10 H0', ['H2']),
              ('H0 H0 H1 CX10 H0 H1 H0 H0 CX10 H0 H0 H0 H1 CX10 H0', ['A9⁼'])])

# A.17: (C4).
D('A17⁼', 1, [('S0 H0 S0 H0 S0 H0', None),
              ('w S0 Sd0 H0 Sd0 S0 H0', ['E']),
              ('w H0 H0', ['S4']),
              ('w', ['H2'])])

# A.18: (C5).
D('A18⁼', 2, [('H0 CX10 H0 H0 CX10 H0', None),
              ('H0 CX10 CX10 H0', ['H2']),
              ('H0 H0', ['A5⁼']),
              ('', ['H2'])])

# A.19: (C6).
D('A19⁼', 2, [('S1 H0 CX10 H0', None), ('H0 CX10 H0 S1', ['A6⁼'])])

# A.20: (C7).
D('A20⁼', 2, [('S0 H0 CX10 H0', None),
              ('S0 H1 CX01 H1', ['A9⁼']),
              ('H1 CX01 H1 S0', ['A19⁼']),
              ('H0 CX10 H0 S0', ['A9⁼'])])

# A.21
D('A21⁼', 2, [('X1 H0 CX10 H0', None),
              ('X1 H0 CX10 H0 X1 X1', ['A2⁼']),
              ('H0 CX10 X1 X0 H0', ['A11⁼']),
              ('H0 CX10 H1 S1 S1 H1 X0 H0', []),
              ('H0 CX10 X1 H0 Z0', ['H2']),
              ('H0 CX10 X1 H0 S0 S0', [])])

# A.22: the mirror of A.21, between two A.9s.
D('A22⁼', 2, [('X0 H0 CX10 H0', None),
              ('X0 H1 CX01 H1', ['A9⁼']),
              ('H1 CX01 X0 H1 S1 S1', ['A21⁼']),
              ('H0 CX10 H0 X0 S1 S1', ['A9⁼'])])

# A.23: (C10).
D('A23⁼', 2, [('H0 CX10 H1 H0 H0 CX10 H0', None),
              ('wd H0 CX10 S1 H1 S1 H1 S1 H0 H0 CX10 H0', ['A4⁼']),
              ('wd S1 H0 CX10 H1 H0 S1 H1 H0 CX10 H0 S1', ['A6⁼']),
              ('wd S1 H1 H0 H0 CX01 S1 CX01 H1 H0 H0 S1', ['A8⁼', 'A9⁼']),
              ('wd S1 H1 CX01 S1 CX01 H1 S1', ['H2']),
              ('wd S1 H1 CX01 S1 Sd0 S0 CX01 H1 S1', ['S4']),
              ('wd S1 H1 Sd0 CX01 S1 CX01 S0 H1 S1', ['A6⁼']),
              ('wd S1 H1 Sd0 CX10 S0 CX10 S0 H1 S1', ['A7⁼']),
              ('wd S1 H1 Z1 Sd0 Z0 CX10 Z0 S0 CX10 S0 H1 S1', ['A12⁼', 'S4', 'A6⁼']),
              ('wd S1 H1 Z1 S0 CX10 Sd0 CX10 S0 H1 S1', ['S4']),
              ('wd S1 H1 S1 S1 S0 CX10 Sd0 CX10 S0 H1 S1', []),
              ('wd S1 H1 S1 S0 CX10 Sd0 CX10 S1 H1 S1 S0', ['A6⁼']),
              ('wd S1 H1 H0 CX10 H0 S1 H1 S1 S0', ['CZ', 'E'])])

# A.24: (C11), the mirror of A.23 between A.9s.
D('A24⁼', 2, [('H0 CX10 H0 H0 H0 CX10 H0', None),
              ('H1 CX01 H1 H0 H1 CX01 H1', ['A9⁼']),
              ('wd S0 H0 H1 CX01 H1 S0 H0 S0 S1', ['A23⁼']),
              ('wd S0 H0 H0 CX10 H0 S0 H0 S0 S1', ['A9⁼'])])


# The paper's own chains for CliffT₂ (its Appendix D.3), read from its
# LaTeX source (paper.py), each figure read by figparse.py.  A label of
# the paper's names an axiom, a shortcut's definition (already spelled
# out: it cites nothing), or one of these chains, named after it.
import paper
from circ import parse

TL = {'t-w8': 'w8', 't-Tpow8': 'T8', 't-H2': 'H2', 't-E': 'E', 't-TX': 'TX', 't-Ct': 'Ct',
      't-B': 'B', 't-CZ': 'CZ', 't-CsCh': 'CsCh', 't-HTHT': 'HTHT', 't-C20': 'HTH',
      't-CX2': 'A5⁼', 't-Z2': 'A1⁼', 't-X2': 'A2⁼', 't-XSX': 'A3⁼',
      't-phasegadget': ['A7⁼', 'A7d⁼'], 't-CNOTHH': 'A8⁼', 't-czrev': 'A9⁼',
      't-XcommutCNOT': 'A10⁼', 't-wCNOT': 'A11⁼', 't-zCNOT': 'A12⁼',
      't-S': None, 't-Sdagger': None, 't-Z': None, 't-X': None, 't-Tdagger': None,
      't-CnotWhite': None, 't-Ch': None, 't-ChWhite': None, 't-Cs': None,
      't-Csdagger': None}

CHAINS = ['t-HX', 't-C', 't-phasegadgetCS', 't-HCh',
          't-CNOTCH', 't-CtrlH', 't-XCHX', 't-CHCH', 't-CSCSCSCS', 't-CSCS', 't-SdCS',
          't-SCSd', 't-HSTH', 'lem:t-C17-dec-eq', 'lem:t-C18-dec-eq', 'lem:t-C19-dec-eq']


def lname(l):
    if l.startswith('lem:t-') and l.endswith('-dec-eq'):
        return 'D' + l[6:-7] + '⁼'
    return l + '⁼'


def width(lines):
    ws = [w for t, _ in lines for (k, w) in parse(t) if w is not None]
    return 1 + max(w + (1 if k in ('CX', 'SW') else 0) for k, w in zip(
        [k for t, _ in lines for (k, w) in parse(t) if w is not None], ws)) if ws else 1


if len(sys.argv) > 1 and sys.argv[1] == 'chains':
    ds = paper.derivations('appendix_cliffordplust.tex')
    for l in CHAINS:
        ls = paper.lines(ds[l], TL)
        D(lname(l), width(ls), ls)
        TL[l] = lname(l)

if len(sys.argv) > 1 and sys.argv[1] == 'probe':
    for k, (l, r) in BS.items():
        try:
            D('P-' + k, 2, [(bdecode(l), None), (bdecode(r), None)], mirror=False)
            print('OK  ', k, flush=True)
        except SystemExit as e:
            print('FAIL', k, flush=True)
