"""CliffT₂'s auxiliary derivations, and the source relations decoded and
derived in CliffT₂: Bian and Selinger's on two wires (the paper's
Appendices D.3 and G.4), and the two-level relations in dimension 2 on
one wire.  Lines are in the notation of circ.gparse with tcliff's
spellings (S is T T); the labels name each step's equations.

Three parts: Cliff₂'s chains of Appendix A ported (S is T T here); the
paper's own Clifford+T chains, read from its LaTeX source by paper.py
(with $BLAKE_SRC the unpacked arXiv source; otherwise from the cache
tpaper.py that such a reading writes), with lines inserted where a step
is too long for the search (FIX) and labels added where a step uses
more than it cites (XL, AFTER, BEFORE); and the decodings.

    python3 mkmod.py tappendix Examples.Independence.Clifford+T.Derivations         'TITLE' ../Clifford+T/Derivations.agda

writes the Agda module.  Run as a script, `tappendix.py MODE [CHAIN]`
runs a part (chains, tl, bs, probe), stopping after CHAIN; with $TCKPT a
file, each chain checkpoints the state there, and with $TRESUME set a
run starts after the last chain checkpointed."""
import sys
import tcliff
from tcliff import LIB, OUT, derive, add_mirror, placed, nat
import frag
from bst import C as BS, D as bdecode, F as bforward


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
# ... equivalently, Z on the target leaves Z on both wires (the paper's
# t-zCNOT).
D('A12t⁼', 2, [('CX10 Z0', None),
               ('Z0 Z0 CX10 Z0', ['A1⁼']),
               ('Z0 CX10 Z1', ['A12⁼']),
               ('Z0 Z1 CX10', ['A6⁼'])])

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

TL = {'t-w8': 'w8', 't-Tpow8': 'T8', 't-H2': 'H2', 't-E': 'E', 't-TX': ['TX', 'XTX⁼', 'XTdX⁼', 'A2⁼', 'w8'], 't-Ct': 'Ct',
      't-B': 'B', 't-CZ': 'CZ', 't-CsCh': 'CsCh', 't-HTHT': 'HTHT', 't-C20': 'HTH',
      't-CX2': 'A5⁼', 't-Z2': 'A1⁼', 't-X2': 'A2⁼', 't-XSX': 'A3⁼',
      't-phasegadget': ['A7⁼', 'A7d⁼'], 't-CNOTHH': 'A8⁼', 't-czrev': 'A9⁼',
      't-XcommutCNOT': 'A10⁼', 't-wCNOT': 'A11⁼', 't-zCNOT': ['A12⁼', 'A12t⁼'],
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




def tdagger_C():
    # T† on the control passes the CNOT: one T at a time.
    ls = [('T1 ' * 7 + 'CX10', None)]
    for k in range(1, 8):
        ls.append(('T1 ' * (7 - k) + 'CX10' + ' T1' * k, ['t-C⁼']))
    D('t-Cd⁼', 2, ls)
    return ['t-Cd⁼']


def tdagger_gadget():
    # The phase gadget with T†: seven gadgets with T.
    ls = [('CX10 Td0 CX10', None), (' '.join(['CX10 T0 CX10'] * 7), ['A5⁼'])]
    for k in range(1, 8):
        ls.append((' '.join(['CX01 T1 CX01'] * k + ['CX10 T0 CX10'] * (7 - k)),
                   ['t-phasegadgetCS⁼']))
    for j in range(2, 8):
        ls.append((' '.join(['CX01'] + ['T1'] * j + ['CX01'] + ['CX01 T1 CX01'] * (7 - j)),
                   ['A5⁼']))
    D('t-phasegadgetCSd⁼', 2, ls)
    # So T on the target passes CS (both being diagonal), and with it S,
    # S† and T†, one T at a time.
    D('TCS⁼', 2, [('T0 CS10', None),
                  ('T1 T0 T0 CX01 Td1 CX01', ['t-phasegadgetCSd⁼']),
                  ('T1 T0 CX01 Td1 CX01 T0', ['t-C⁼']),
                  ('CS10 T0', ['t-phasegadgetCSd⁼'])])
    for name, k in [('SCS⁼', 2), ('SdCS⁼', 6), ('TdCS⁼', 7)]:
        D(name, 2, [('T0 ' * k + 'CS10', None)] +
          [('T0 ' * (k - j) + 'CS10' + ' T0' * j, ['TCS⁼']) for j in range(1, k + 1)])
    return ['t-phasegadgetCSd⁼', 'TCS⁼', 'SCS⁼', 'SdCS⁼', 'TdCS⁼']


# Lines inserted before a line of the paper's, with that line's labels
# or their own, where its step is too long for the search.
def _cs4(cs):
    G = 'CX10 Td0 CX10'
    return ' '.join('T0 ' + 'T1 ' * c + G for c in cs)


def _cs4b(cs):
    G = 'CX01 Td1 CX01'
    return ' '.join(['T0 ' * cs[0] + 'Z1 ' + G] + ['T0 ' * c + G for c in cs[1:]])


def _cs4g(k):
    G, Gb = 'CX10 Td0 CX10', 'CX01 Td1 CX01'
    return ' '.join(['T0 Z1 ' + (Gb if k > 0 else G)] +
                    ['T0 ' + (Gb if i < k else G) for i in range(1, 4)])


G3 = 'CX10 Td0 CX10'
MOVES = [(1, 1, 2, 0), (1, 2, 1, 0), (1, 3, 0, 0), (2, 2, 0, 0), (3, 1, 0, 0)]
FIX = {('t-CSCSCSCS', 2): [_cs4(c) for c in MOVES],
       ('t-CSCSCSCS', 3): [_cs4g(k) for k in range(1, 4)],
       ('t-CSCSCSCS', 4): [_cs4b(c) for c in MOVES],
       ('t-CSCSCSCS', 7): [('Z0 CX01 Z0 CX01', ['A12⁼']), ('CX01 Z0 Z0 CX01', ['A6⁼'])],
       ('t-SdCS', 4): [('T1 Td0 X1 X1 CX01 Td1 CX01', ['A2⁼']),
                       ('T1 Td0 X1 X1 CX01 Td1 X1 X1 CX01', ['A2⁼'])],
       ('t-SdCS', 7): [('X1 T1 T1 T1 T0 Z0 Z1 CX01 Z1 Z1 T1 CX01 X1 T0 T0', ['A1⁼']),
                       ('X1 T1 T1 T1 T0 Z0 CX01 Z0 Z1 T1 CX01 X1 T0 T0', ['A12⁼']),
                       ('X1 T1 T1 T1 T0 CX01 Z0 Z0 Z1 T1 CX01 X1 T0 T0', ['A6⁼']),
                       ('X1 T1 T1 T1 T0 CX01 Z1 T1 CX01 X1 T0 T0', ['A1⁼'])],
       ('t-HSTH', 9): [('X1 CS10 X1 CH10 T0 CHo10 Td0 Sd0 CS10', ['SdCS⁼'])],
       ('t-HSTH', 14): [('S0 CSd10 T0 CHo10 Td0 X1 CSd10 X1 CH10', ['t-SCSd⁼', 'A2⁼']),
                        ('S0 CSd10 T0 CHo10 Td0 Sd0 CS10 CH10', ['t-SdCS⁼', 'A2⁼'])],
       ('t-HSTH', 15): [('S0 T0 CSd10 CHo10 Td0 CS10 Sd0 CH10', ['TCS⁼'])],
       ('t-SdCS', 12): ['X1 T1 T1 T0 %s T1 T0 %s T0 %s X1' % ((G3,) * 3),
                        'X1 T1 T0 %s T1 T1 T0 %s T0 %s X1' % ((G3,) * 3)]}

# Labels a line of the paper's needs besides those it cites.
XL = {('t-SdCS', 8): ['T8'],
      ('lem:t-C19-dec-eq', 6): ['GCS⁼'],
      ('lem:t-C19-dec-eq', 13): ['T1CS⁼', 'Td1CS⁼', 't-Cd⁼'],
      ('lem:t-C19-dec-eq', 18): ['CSdD⁼'],
      ('lem:t-C19-dec-eq', 24): ['T0CSd⁼', 'S0CSd⁼'],
      ('lem:t-C19-dec-eq', 26): ['Td0CSd⁼', 'Sd0CSd⁼']}


def gadget_CS():
    # The gadget with T† is CS followed by T† on both wires.
    D('GCS⁼', 2, [('CX10 Td0 CX10', None),
                  ('CX10 Td0 CX10 T1 Td1 T0 Td0', ['T8']),
                  ('T1 CX10 Td0 CX10 Td1 T0 Td0', ['t-C⁼']),
                  ('T1 CX01 Td1 CX01 T0 Td1 Td0', ['t-phasegadgetCSd⁼']),
                  ('T1 T0 CX01 Td1 CX01 Td1 Td0', ['t-C⁼']),
                  ('CS10 Td1 Td0', ['t-phasegadgetCSd⁼'])])
    # T on the control passes CS, and so T†.
    D('T1CS⁼', 2, [('T1 CS10', None), ('CS10 T1', ['t-C⁼'])])
    D('Td1CS⁼', 2, [('T1 ' * 7 + 'CS10', None)] +
      [('T1 ' * (7 - j) + 'CS10' + ' T1' * j, ['T1CS⁼']) for j in range(1, 8)])
    # T on the target passes the gadget.
    D('TG⁼', 2, [('T0 CX10 Td0 CX10', None),
                 ('T0 CX01 Td1 CX01', ['t-phasegadgetCSd⁼']),
                 ('CX01 Td1 CX01 T0', ['t-C⁼']),
                 ('CX10 Td0 CX10 T0', ['t-phasegadgetCSd⁼'])])
    # The phases on wire 0 pass CS† = CS³.
    D('T0CSd⁼', 2, [('T0 CS10 CS10 CS10', None),
                    ('CS10 T0 CS10 CS10', ['TCS⁼']),
                    ('CS10 CS10 T0 CS10', ['TCS⁼']),
                    ('CSd10 T0', ['TCS⁼'])])
    for name, k in [('S0CSd⁼', 2), ('Sd0CSd⁼', 6), ('Td0CSd⁼', 7)]:
        D(name, 2, [('T0 ' * k + 'CSd10', None)] +
          [('T0 ' * (k - j) + 'CSd10' + ' T0' * j, ['T0CSd⁼']) for j in range(1, k + 1)])
    # CS† = CS³ is T† ⊗ T† followed by the gadget with T.
    G = 'CX10 Td0 CX10'
    D('CSdD⁼', 2, [('CSd10', None),
                   ('T1 T1 T0 %s T0 %s T1 T0 %s' % (G, G, G), ['T1CS⁼', 't-C⁼']),
                   ('T1 T1 T1 T0 %s T0 %s T0 %s' % (G, G, G), ['t-C⁼']),
                   ('T1 T1 T1 T0 T0 %s %s T0 %s' % (G, G, G), ['TG⁼']),
                   ('T1 T1 T1 T0 T0 T0 %s %s %s' % (G, G, G), ['TG⁼']),
                   ('T1 T1 T1 T0 T0 T0 CX10 Td0 Td0 Td0 CX10', ['A5⁼']),
                   ('T1 T1 T1 T0 T0 T0 CX10 Z0 T0 CX10', ['T8']),
                   ('T1 T1 T1 T0 T0 T0 Z1 Z0 CX10 T0 CX10', ['A12t⁼']),
                   ('Td1 Td0 CX10 T0 CX10', [])])


# Lemmas a chain needs, derived just before it.
BEFORE = {'lem:t-C19-dec-eq': gadget_CS}


def fixed(l, ls):
    out = []
    for i, (t, labs) in enumerate(ls):
        out += [x if isinstance(x, tuple) else (x, labs) for x in FIX.get((l, i), [])]
        out.append((t, labs if labs is None else labs + XL.get((l, i), [])))
    return out


# What a chain's label cites besides the chain itself.
AFTER = {'t-C': tdagger_C, 't-phasegadgetCS': tdagger_gadget,
         # X-conjugations: X X = ε cancels what they leave.
         # and the diagonal gates on wire 0 pass CS either way.
         't-XCHX': lambda: ['A2⁼'],
         't-SdCS': lambda: ['A2⁼', 'TCS⁼', 'SCS⁼', 'SdCS⁼', 'TdCS⁼'],
         't-SCSd': lambda: ['A2⁼', 'TCS⁼', 'SCS⁼', 'SdCS⁼', 'TdCS⁼']}

# Run as a script, a mode ('chains', 'tl', 'bs', 'probe'; chains and bs
# take the chain to stop after); imported by mkmod.py, everything.
MAIN = __name__ == '__main__'
MODE = sys.argv[1] if MAIN and len(sys.argv) > 1 else 'all'
UPTO = sys.argv[2] if MAIN and len(sys.argv) > 2 else None

# A checkpoint after each chain (the file named by $TCKPT), from which a
# later run resumes when $TRESUME is set: for working on a chain without
# rederiving the ones before it.
import os
import pickle
CKPT = os.environ.get('TCKPT')
STATE = ['LIB', 'OUT', 'MIRROR', 'NATS', 'LABEL', 'CORE', 'SWAPS2', 'SWAPS3', 'NATLABELS']


def save(last):
    with open(CKPT, 'wb') as f:
        pickle.dump({'last': last, 'TL': TL, **{k: getattr(frag, k) for k in STATE}}, f)


def restore():
    with open(CKPT, 'rb') as f:
        st = pickle.load(f)
    for k in STATE:
        x = getattr(frag, k)
        if isinstance(x, dict):
            x.clear()
            x.update(st[k])
        else:
            x[:] = st[k]
    TL.clear()
    TL.update(st['TL'])
    return CHAINS.index(st['last']) + 1


if MODE in ('all', 'chains', 'bs'):
    ds = paper.transcribed('appendix_cliffordplust.tex', CHAINS, 'tpaper.py')
    start = restore() if CKPT and os.environ.get('TRESUME') else 0
    for l in CHAINS[start:]:
        if l in BEFORE:
            BEFORE[l]()
        ls = fixed(l, paper.lines(ds[l], TL))
        D(lname(l), width(ls), ls)
        TL[l] = [lname(l)] + (AFTER[l]() if l in AFTER else [])
        if CKPT:
            save(l)
        if l == UPTO:
            break


# Lemma 20 on one wire: the two-level relations of Table 3.1 in
# dimension 2 (Examples.Groups.Clifford+T-2qubit-TwoLevel, the instances
# with distinct indices), decoded — ω_[0] as ω T†, ω_[1] as T, X_[0,1]
# as X, H_[0,1] as H — and read backwards.  In dimension 1 only ω_[0]⁸
# is left, which is the axiom ω⁸.
TLD = {'w0': 'w Td0', 'w1': 'T0', 'X': 'X0', 'H': 'H0'}


def tldec(word):
    return ' '.join(TLD[g] for g in reversed(word))


TL2 = [('order-ω₀', ['w0'] * 8, []),
       ('order-ω₁', ['w1'] * 8, []),
       ('order-H', ['H', 'H'], []),
       ('order-X', ['X', 'X'], []),
       ('comm-ωω', ['w0', 'w1'], ['w1', 'w0']),
       ('comm-ωω′', ['w1', 'w0'], ['w0', 'w1']),
       ('swap-Xω', ['X', 'w1'], ['w0', 'X']),
       ('swap-Xω′', ['X', 'w0'], ['w1', 'X']),
       ('scalar-X', ['w0', 'w1', 'X'], ['X', 'w0', 'w1']),
       ('scalar-H', ['w0', 'w1', 'H'], ['H', 'w0', 'w1']),
       ('rel-18', ['H', 'X'], ['w1'] * 4 + ['H']),
       ('rel-19', ['H', 'w0', 'w0', 'H'], ['w0'] * 6 + ['H'] + ['w0'] * 3 + ['w1'] * 5)]

WAY = {'order-ω₀': [('w8 ' + 'Td0 ' * 8, [])] +
                  [(' '.join(['T0'] * (56 - 8 * k)), ['T8', 'w8']) for k in range(1, 7)],
       'rel-19': [('w w H0 Sd0 H0', None), ('w S0 H0 S0', None)] +
                 [('w ' + 'T0 ' * (2 + 8 * a) + 'H0 T0 T0', ['T8']) for a in range(1, 4)] +
                 [('w ' + 'T0 ' * 26 + 'H0' + ' T0' * (2 + 8 * b), ['T8']) for b in range(1, 6)] +
                 [('w9 ' + 'T0 ' * 5 + 'Td0 ' * 3 + 'H0' + ' Td0' * 6, ['w8'])]}

if MODE in ('all', 'tl'):
    for k, l, r in TL2:
        D('DTL-' + k + '⁼', 1,
          [(tldec(l), None)] + WAY.get(k, []) + [(tldec(r), None)], mirror=False)
    # Lemma 19 on one wire: ω, encoded as ω_[0] ω_[1], decoded.
    D('Dω₁⁼', 1, [('T0 w Td0', None), ('w', ['T8'])], mirror=False)

# Lemma 20 on two wires: Bian and Selinger's relations (bst.py), decoded
# as the paper reads them, in the order written (the encoding keeps the
# order of the gates: Clifford+T.Bridge); comm-W, that ω is central, is
# Central-Scalars'.  The five involving T past the Clifford ones go
# through the paper's decoding lemmas (its G.4), in their mirror images
# where the paper's qubits are the other way up.
# Their CNOT onto qubit 1 decodes to H H CNOT H H, which A.8 turns into
# the CNOT from wire 0, and their controlled H onto qubit 1 then to the
# swap around ours (CH↓).
HARD = {'comm-T0-CZ': ['A9⁼', 't-C⁼'],
        'swap-T0': ['DC17⁼', 'A9⁼', 'A8⁼']}
CX1 = ['A8⁼', 'H2']
CH1 = 'S1 H1 T1 H1 H0 CX10 H0 H1 Td1 H1 Sd1'        # their CH1, decoded
WAYBS = {'rel-A': [('CX01 T1 H1 Td1 CX01 X1 T1 H1 Td1', CX1),
                   ('T1 H1 Td1 CX01 X1 T1 H1 Td1 CX01', ['DC18⁼'])],
         'rel-B': [('CX01 T1 H1 T1 H1 Td1 CX01 X1 T1 H1 Td1 H1 Td1', CX1),
                   ('T1 H1 T1 H1 Td1 CX01 X1 T1 H1 Td1 H1 Td1 CX01', ['DC19⁼'])],
         'rel-C': [('%s H1 T1 %s CH10 H0 T0 CH10' % (CH1, CH1), ['H2']),
                   ('SW01 CH10 SW01 H1 T1 SW01 CH10 SW01 CH10 H0 T0 CH10', ['CH↓⁼']),
                   ('SW01 CHo10 SW01 T1 SW01 CH10 SW01 CHo10 T0 CH10', ['σH′⁼', 'sH']),
                   ('CHo10 T0 CH10 SW01 CHo10 SW01 T1 SW01 CH10 SW01', ['HTH']),
                   ('CH10 H0 T0 CH10 SW01 CH10 SW01 H1 T1 SW01 CH10 SW01', ['σH′⁼', 'sH']),
                   ('CH10 H0 T0 CH10 %s H1 T1 %s' % (CH1, CH1), ['CH↓⁼'])]}
LAST = {'rel-A': CX1, 'rel-B': CX1, 'rel-C': ['H2']}


def swapped_CH():
    # Their controlled H onto qubit 1, decoded, is ours under the swap:
    # the swap passes its single-wire letters one at a time.
    P, Q = ['T', 'T', 'H', 'T'], ['T'] * 7 + ['H'] + ['T'] * 6

    def line(i, j):
        return ' '.join([p + '1' for p in P[:4 - i]] + ['SW01'] + [p + '0' for p in P[4 - i:]] +
                        ['CX10'] + [q + '0' for q in Q[:j]] + ['SW01'] + [q + '1' for q in Q[j:]])
    sw = ['sT', 'sH', 'σT′⁼', 'σH′⁼']
    D('CH↓⁼', 2, [(CH1, None),
                  ('S1 H1 T1 CX01 Td1 H1 Sd1', CX1)] +
      [(line(i, 0), sw) for i in range(1, 5)] + [(line(4, j), sw) for j in range(1, 15)],
      mirror=False)

if MODE in ('all', 'bs'):
    swapped_CH()
    only = os.environ.get('TONLY')          # while working on some of them
    for k, (l, r) in BS.items():
        if k.startswith('comm-W') or (only and k not in only.split(',')):
            continue
        D('DBS-' + k + '⁼', 2, [(bforward(l), None)] + WAYBS.get(k, []) +
          [(bforward(r), LAST.get(k, HARD.get(k)))], mirror=False)
    # Lemma 19 on two wires: CNOT, encoded as H CZ H, and the swap, as
    # three such CNOTs, decoded.
    D('DCX⁼', 2, [('H0 H0 CX10 H0 H0', None), ('CX10', ['H2'])], mirror=False)
    D('Dσ⁼', 2, [('H0 H0 CX10 H0 H0 H1 H0 CX10 H0 H1 H0 H0 CX10 H0 H0', None),
                 ('CX10 H1 H0 CX10 H0 H1 CX10', ['H2']),
                 ('CX10 CX01 CX10', ['A9⁼']),
                 ('SW01 CX10 CX10', ['B']),
                 ('SW01', ['A5⁼'])], mirror=False)

if MODE == 'probe':
    for k, (l, r) in BS.items():
        try:
            D('P-' + k, 2, [(bdecode(l), None), (bdecode(r), None)], mirror=False)
            print('OK  ', k, flush=True)
        except SystemExit as e:
            print('FAIL', k, flush=True)
