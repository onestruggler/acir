"""CliffCS₂'s auxiliary derivations, and the source relations decoded and
derived in CliffCS₂: Bian and Selinger's on three wires (the paper's
Appendices D.5 and G.5), and the two-level relations in dimensions 2 and
4 on one and two wires.  Lines are in the notation of circ.gparse with
cscliff's spellings (CX is H CS CS H on its target); the labels name
each step's equations.

The paper's Clifford+CS chains are read from its LaTeX source by
paper.py (with $BLAKE_SRC the unpacked arXiv source; otherwise from the
cache cspaper.py that such a reading writes) and run by chains.py.

    python3 mkmod.py csappendix Examples.Independence.Clifford+CS.Derivations \\
        'TITLE' ../Clifford+CS/Derivations.agda

writes the Agda module.  Run as a script, `csappendix.py MODE [CHAIN]`
runs a part (chains, ...), stopping after CHAIN; $TCKPT and $TRESUME
checkpoint and resume as chains.py says."""
import os
import re
import sys
import cscliff
from cscliff import LIB, OUT, derive, add_mirror, placed, nat
import frag
import chains


PROBE = bool(os.environ.get('TPROBE'))      # report a failed derivation and go on


def D(name, width, lines, **kw):
    if not PROBE:
        return derive(name, width, lines, **kw)
    try:
        derive(name, width, lines, **kw)
    except SystemExit as e:
        print('PROBE-FAIL', name, str(e).splitlines()[0], flush=True)


def omegas(tok):
    if tok == 'w':
        return 1
    if tok == 'wd':
        return 7
    if tok.startswith('w') and tok[1:].isdigit():
        return int(tok[1:])
    return None


def scal_lines(text):
    """From a line to the same with its scalars gathered at the front and
    reduced mod 8, ω⁸ at a time: the lines between, each a step by ω⁸ = ε
    (moving the scalars is a permutation)."""
    toks = text.split()
    q = sum(omegas(t) or 0 for t in toks)
    rest = ' '.join(t for t in toks if omegas(t) is None)
    out = []
    while True:
        out.append(((('w%d ' % q) if q else '') + rest).strip())
        if q < 8:
            return out
        q -= 8


def normalised(left, right, labels):
    """Lines from left to right: both normalised, the step between them
    citing labels."""
    ls, rs = scal_lines(left), scal_lines(right)
    return ([(left, None)] + [(t, ['w8']) for t in ls] + [(rs[-1], labels)] +
            [(t, ['w8']) for t in reversed(rs[:-1])] + [(right, ['w8'])])


MAIN = __name__ == '__main__'
MODE = sys.argv[1] if MAIN and len(sys.argv) > 1 else 'all'
UPTO = sys.argv[2] if MAIN and len(sys.argv) > 2 else None

# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σS′⁼', 2, [('SW01 S0', None), ('S1 SW01', ['sS', 'ss'])])
NATLABELS = frag.NATLABELS
NATLABELS += ['σH′⁼', 'σS′⁼']
for n in ['CPh⁼', 'B⁼', 'XCS⁼', 'CE⁼']:
    add_mirror(n)

# CNOT with its target on wire 1 is CNOT with its target on wire 0 under
# the swap (the swap passes H, and CS by (CSr)).
D('CXd⁼', 2, [('SW01 CX10 SW01', None), ('CX01', ['σH′⁼', 'sH', 'CSr', 'ss'])])
# (I) spells CNOT from wire 2 onto wire 0 as the swap around CX₂₁.
D('CX20s⁼', 3, [('SW01 CX21 SW01', None), ('CX20', ['σH′⁼', 'sH', 'ss'])], mirror=False)


# ---------------------------------------------------------------------
# The paper's own chains for CliffCS₂ (its Appendix D.5).  A label of
# the paper's names an axiom, a shortcut's definition (already spelled
# out: it cites nothing), or one of these chains, named after it.

RENAME = {'cs-w8': 'w8', 'cs-H2': 'H2', 'cs-S4': 'S4', 'cs-E': 'E', 'cs-C': 'Ct',
          'cs-CSrev': 'CSr', 'cs-B': ['B', 'CXd⁼'], 'cs-XCS': 'XCS', 'cs-SHCHC': 'CE', 'cs-I': 'I',
          'cs-U': ['SH₀⁼', 'SH₁⁼', 'SH₂⁼', 'SH₃⁼'],
          'cs-CNOT': None, 'cs-X': None, 'cs-Z': None, 'cs-Sdagger': None,
          'cs-wdagger': None}

CHAINS = ['lem:cs-C4-dec-eq', 'lem:cs-C5-dec-eq', 'lem:cs-C6-dec-eq', 'lem:cs-C7-dec-eq',
          'lem:cs-C8-dec-eq', 'lem:cs-C9-dec-eq', 'lem:cs-C11-dec-eq', 'lem:cs-C12-dec-eq',
          'lem:cs-C13-dec-eq', 'lem:cs-C14-dec-eq', 'lem:cs-C15-dec-eq',
          'lem:cs-C17-dec-eq', 'lem:cs-dswap-unfolding']


def lname(l):
    if l.startswith('lem:cs-') and l.endswith('-dec-eq'):
        return 'D' + l[7:-7] + '⁼'
    if l == 'lem:cs-dswap-unfolding':
        return 'Dσu⁼'
    return l + '⁼'


X14 = 'CX01 CZ21 CX21 CX01 CX21'
P14 = 'CZ20 CZ20 CZ21 CZ21 CZ21 CX01 CZ21'
FIX = {('lem:cs-C14-dec-eq', 5): [
    ('CZ10 CZ10 CZ10 CZ20 CZ20 CZ21 CZ21 CZ10 CZ21 ' + X14, ['DC12⁼']),
    ('CZ10 CZ10 CZ10 CZ20 CZ20 CZ10 CZ21 CZ21 CZ21 ' + X14, ['DC12⁼']),
    ('CZ10 CZ10 CZ10 CZ20 CZ10 CZ20 CZ21 CZ21 CZ21 ' + X14, ['DC12ˢ⁰⁼']),
    ('CZ10 CZ10 CZ10 CZ10 CZ20 CZ20 CZ21 CZ21 CZ21 ' + X14, ['DC12ˢ⁰⁼'])],
       # CX₂₁ CX₀₁ CX₂₁ = CX₀₁, by H H = ε, (C12) and (C5).
       ('lem:cs-C14-dec-eq', 6): [(P14 + ' H1 CS21 CS21 CS10 CS10 CS21 CS21 H1', ['H2']),
                                  (P14 + ' H1 CS10 CS21 CS21 CS10 CS21 CS21 H1', ['DC12⁼']),
                                  (P14 + ' H1 CS10 CS10 CS21 CS21 CS21 CS21 H1', ['DC12⁼'])],
       # CZ₂₀ past CS₂₁, and CZcx with the wires reversed.
       ('lem:cs-C14-dec-eq', 7): [('CZ20 CZ21 CZ21 CZ21 CZ20 CX01 CZ21 CX01', ['DC12ˢ¹⁼']),
                                  ('CZ21 CZ21 CZ21 CZ20 CZ20 CX01 CZ21 CX01', ['DC12ˢ¹⁼']),
                                  ('CZ21 CX01 CZ21 CZ21 CX01 CX01 CZ21 CX01',
                                   ['CZcxˢ⁰¹⁰⁼'])],
       # The swap as three CNOTs spelled with CZ, with ω⁴⁰ = ε eight at a time.
       ('lem:cs-dswap-unfolding', 4): [
           ('H1 H0 CZ10 CZ10 H1 H0 CZ10 CZ10 H1 H0 CZ10 CZ10 w%d' % (8 * j), ['w8', 'H2'])
           for j in range(1, 5)]}
XL = {('lem:cs-C14-dec-eq', 1): ['CZcx⁼', 'CX2⁼'],
      ('lem:cs-C14-dec-eq', 7): ['CX2⁼']}
AFTER = {}


def cnot_cz():
    # CNOT is an involution (CS⁴ = ε, the decoded C5), and conjugates CZ
    # = CS CS linearly ((I), with H on the target).
    D('CX2⁼', 2, [('CX10 CX10', None), ('H0 CS10 CS10 CS10 CS10 H0', ['H2']), ('', ['DC5⁼', 'H2'])])
    # (I) with CX₂₀ CX₂₀ = ε: CX₂₁ CX₁₀ CX₂₁ = CX₁₀ CX₂₀ (CX₂₀ being the
    # swap around CX₂₁, as (I) spells it).
    C20 = 'SW01 CX21 SW01'
    D('CZcx⁼', 3, [('CX21 CS10 CS10 CX21', None),
                   ('H0 CX21 CX10 CX21 H0', ['H2']),
                   ('H0 CX21 CX10 CX21 %s %s H0' % (C20, C20), ['CX2⁼', 'ss']),
                   ('H0 CX21 CX21 CX10 %s H0' % C20, ['I']),
                   ('H0 CX10 %s H0' % C20, ['CX2⁼']),
                   ('CS10 CS10 H0 %s H0' % C20, ['H2']),
                   ('CS10 CS10 SW01 H1 CX21 H1 SW01', ['σH′⁼', 'sH']),
                   ('CS10 CS10 CS20 CS20', ['H2', 'ss'])], mirror=False)
    # CS on the wires 0 1 and 0 2 commute, and on 0 2 and 1 2: (C12)
    # under the swap of 0 1, resp. 1 2.  And CZcx with the wires reversed.
    placed('DC12⁼', [0])
    placed('DC12⁼', [1])
    placed('CZcx⁼', [0, 1, 0])


def cnot_comm():
    # CNOTs with a common control commute, from (I) alone: with A = CX₁₀,
    # B = CX₂₁ and C = CX₂₀ (involutions), (I) is A B C = B A, so B C =
    # A B A, and C B = C B (A B A)(A B A) = C B (B C)(A B A) = A B A.
    placed('CZcx⁼', [1])         # CX₁₂ conjugates CZ₀₂ to CZ₀₂ CZ₀₁
    C = 'SW01 CX21 SW01'
    D('CXI⁼', 3, [('CX21 ' + C, None),
                  ('CX10 CX10 CX21 ' + C, ['CX2⁼']),
                  ('CX10 CX21 CX10', ['I'])], mirror=False)
    D('CXcc⁼', 3, [(C + ' CX21', None),
                   (C + ' CX21 CX10 CX10', ['CX2⁼']),
                   (C + ' CX21 CX10 CX21 CX21 CX10', ['CX2⁼']),
                   (C + ' CX21 CX10 CX21 CX10 CX10 CX21 CX10', ['CX2⁼']),
                   (C + ' CX21 CX21 %s CX10 CX21 CX10' % C, ['CXI⁼']),
                   (C + ' %s CX10 CX21 CX10' % C, ['CX2⁼']),
                   ('CX10 CX21 CX10', ['CX2⁼', 'ss']),
                   ('CX21 ' + C, ['CXI⁼'])], mirror=False)


BEFORE = {'lem:cs-C14-dec-eq': cnot_cz, 'lem:cs-C15-dec-eq': cnot_comm}


def ends(*labels):
    # The chain's two ends, one step citing labels.
    return lambda ch: [(ch[0][0], None), (ch[-1][0], list(labels))]


# The paper moves a whole circuit through the swap in one step; these
# are the mirror images of an equation the generator already has.
REPLACE = {'lem:cs-C9-dec-eq': ends('DC8⁼'), 'lem:cs-C11-dec-eq': ends('CE', 'w8'),
           # Both sides are CZ₀₂: CX₂₁ conjugates CZ₀₁ to CZ₀₁ CZ₀₂ (CZcx),
           # CX₁₂ commutes with CZ₀₁ and conjugates CZ₀₂ to CZ₀₂ CZ₀₁.
           'lem:cs-C15-dec-eq': lambda ch: [
               (ch[0][0], None),
               ('CX12 CS10 CS10 CS20 CS20 CX12', ['CZcx⁼']),
               ('CS10 CS10 CX12 CS20 CS20 CX12', ['DC12⁼']),
               ('CS10 CS10 CS20 CS20 CS10 CS10', ['CZcxˢ¹⁼']),
               ('CS20 CS20', ['DC12ˢ⁰⁼', 'DC5⁼']),
               ('CS10 CS10 CS20 CS20 CS10 CS10', ['DC12ˢ⁰⁼', 'DC5⁼']),
               (ch[-1][0], ['CZcx⁼'])]}

CORRECT = {}

CH = chains.Chains('appendix_cliffordpluscs.tex', CHAINS, RENAME, 'cspaper.py', lname,
                   FIX, XL, AFTER, BEFORE, REPLACE, CORRECT)
if MODE in ('all', 'chains', 'bs', 'tl'):
    CH.run(D, UPTO)


# ---------------------------------------------------------------------
# Lemma 20 on three wires: Bian and Selinger's relations (bscs.py),
# decoded as the paper reads them, in the order written; the encoding
# keeps the order of the gates (Clifford+CS.Bridge).  The citations
# follow the paper's G.5.

from bscs import C as BS3, F as bforward


def bs_labels(k):
    base = ['w8', 'H2']
    if k.startswith('ax-CS01-CS01-CS01-CS01') or k.startswith('ax-CS12-CS12-CS12-CS12'):
        return base + ['DC5⁼']
    if re.match(r'ax-CS\d\d-S\d=S\d-CS', k):
        return base + ['DC6⁼', 'DC7⁼']
    if k.startswith('ax-CS12-CS01'):
        return base + ['DC12⁼']
    if k.startswith('ax-S0-S0-S0') or k.startswith('ax-S1-S1-S1') or k.startswith('ax-S2-S2-S2'):
        return base + ['S4']
    if re.match(r'ax-S\d-K\d-S\d-K\d-S\d-K\d', k):
        return base + ['DC4⁼']
    if re.match(r'ax-X\d-CS', k):
        return base + ['DC8⁼', 'DC9⁼']
    if re.match(r'ax-CS\d\d-K\d-CS\d\d-K\d-S\d=', k):
        return base + ['DC11⁼', 'CE']
    if k.startswith('ax-CX10-CX01-CS12-CX01'):
        return base + ['DC13⁼']
    if k.startswith('ax-CX10-CX01-CS12-CS12'):
        return base + ['DC15ˢ⁰¹⁰⁼']
    if k.startswith('ax-CS12-CX01'):
        return base + ['DC14⁼']
    if k.startswith('ax-CS12-K1-CS12-K1-CS01'):
        return base + ['SH₁⁼']
    if k.startswith('ax-CS12-K1-CS12-CS12-CS12'):
        return base + ['DC17⁼']
    return base


if MODE in ('all', 'bs'):
    placed('DC15⁼', [0, 1, 0])
    only = os.environ.get('TONLY')          # while working on some of them
    for k, (l, r) in BS3.items():
        if only and k not in only.split(','):
            continue
        D('DBS-' + k[3:] + '⁼', 3, normalised(bforward(l), bforward(r), bs_labels(k)),
          mirror=False)
    # Lemma 19 on three wires: the swap, encoded as their Swap01 (three
    # CNOTs), decoded.
    from bscs import expand
    D('DSwap⁼', 2, normalised(bforward(expand(['Swap01'])), 'SW01',
                              ['B', 'CXd⁼', 'CX2⁼', 'Dσu⁼', 'H2']), mirror=False)


# ---------------------------------------------------------------------
# Lemma 20 on one and two wires: the two-level relations in dimensions
# 2 and 4 (tlcs.py), decoded in the order written.

import tlcs

TL_LABELS = ['w8', 'H2', 'S4', 'E', 'Ct', 'CSr', 'B', 'XCS', 'CE', 'CXd⁼', 'CX2⁼',
             'DC4⁼', 'DC5⁼', 'DC6⁼', 'DC7⁼', 'DC8⁼', 'DC9⁼', 'DC11⁼']

if MODE in ('all', 'tl'):
    only = os.environ.get('TONLY')
    # The scalar i, on every index, decoded: ω ω S† S on one wire.
    D('DJ1⁼', 1, [('w w Sd0 S0', None), ('w w', ['S4'])], mirror=False)
    widths = [int(x) for x in os.environ.get('TLWIDTHS', '1,2').split(',')]
    if 1 in widths:
        for k, l, r in tlcs.relations(2):
            if only and k not in only.split(','):
                continue
            D('DTL1-%s⁼' % k, 1,
              normalised(tlcs.decode(tlcs.D1, l), tlcs.decode(tlcs.D1, r), TL_LABELS),
              mirror=False)
    # On two wires, one standard instance of each relation, the others
    # by transport along the permutations of the indices (tl2.py).
    if 2 in widths:
        import tl2
        tl2.run(D)
