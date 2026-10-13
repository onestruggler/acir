"""G.5 of Blake's paper: Bian and Selinger's 3-qubit Clifford+CS
relations, decoded, derived in CliffCS₂.

The decoding reads a word of theirs letter for letter (cs3.py: every
gate matrix is symmetric, so no reversal is needed), qubit k on wire k,
K as ω⁷ H and the scalar i as ω².  The decoded relations are then the
paper's (C1)–(C17) up to scalars ω⁸ and the reflection of the wires:
the commutations are trace equalities or E.3, E.4, E.8; the X–CS and
CS–K relations are (XCS) and (CE) on either wire (E.5–E.7); and the
3-qubit ones are E.9–E.12, (SH₁), and E.11 under the reflection of the
wires.  Each equation is stated on the decoded letters exactly, so that
the Agda decoding function produces its sides."""
from appendixE import D, LIB, OUT, placed
import cs3
from cs3 import R, text

first = len(OUT)

NAME = {k: 'D' + k[3:] + '⁼' for k in R}


def strip(t):
    """A line's number of ω letters, and the rest of its tokens."""
    n, rest = 0, []
    for tok in t.split():
        if tok == 'w':
            n += 1
        elif tok == 'wd':
            n += 7
        elif tok[0] == 'w' and tok[1:].isdigit():
            n += int(tok[1:])
        else:
            rest.append(tok)
    return n, ' '.join(rest)


def chain(L, Rt, a, b, labels):
    """L down to its scalars mod 8 (ω⁸ at a time), the equation a = b
    (b with any scalar the equation adds), and up to Rt."""
    n, restL = strip(L)
    lines = [(L, None)]
    while n >= 8:
        n -= 8
        lines.append(('w%d %s' % (n, restL), ['w8']))
    if a != restL:
        lines.append(('w%d %s' % (n, a), []))
    lines.append(('w%d %s' % (n, b), labels))
    m, rest2 = strip(lines[-1][0])
    nR, restR = strip(Rt)
    assert (nR - m) % 8 == 0 and nR >= m, (L, Rt)
    while m < nR:
        m += 8
        lines.append(('w%d %s' % (m, rest2), ['w8']))
    lines.append((Rt, []))
    return lines

# E.11 with the wires reflected.
E11R = placed('E11⁼', [0, 1, 0])

TRIV = ['ax-%s-%s=%s-%s' % (a, b, b, a) for a, b in [
    ('S1', 'S0'), ('S2', 'S0'), ('S2', 'S1'), ('K1', 'K0'), ('K2', 'K0'), ('K2', 'K1'),
    ('CS12', 'S0'), ('CS01', 'S2'), ('S1', 'K0'), ('S2', 'K0'), ('S2', 'K1'),
    ('K1', 'S0'), ('K2', 'S0'), ('K2', 'S1'), ('CS01', 'K2'), ('CS12', 'K0')]]
SIMPLE = {
    'ax-iI-iI-iI-iI=ε': ['w8'],
    'ax-CS01-S0=S0-CS01': ['E4⁼'], 'ax-CS01-S1=S1-CS01': ['E3⁼'],
    'ax-CS12-S1=S1-CS12': ['E4⁼'], 'ax-CS12-S2=S2-CS12': ['E3⁼'],
    'ax-CS12-CS01=CS01-CS12': ['E8⁼'],
    'ax-S0-S0-S0-S0=ε': ['S4'], 'ax-S1-S1-S1-S1=ε': ['S4'], 'ax-S2-S2-S2-S2=ε': ['S4'],
    'ax-CS01-CS01-CS01-CS01=ε': ['E2⁼'], 'ax-CS12-CS12-CS12-CS12=ε': ['E2⁼'],
}
# Rules whose decoded sides are a known equation's, up to ω⁸: the
# equation's two sides, scalars apart, and its name.
VIA = {
    'ax-X0-CS01=CS01-CS01-CS01-X0-S1': ('X0 CS01', 'CS01 CS01 CS01 X0 S1', ['XCS↓⁼']),
    'ax-X1-CS01=CS01-CS01-CS01-X1-S0': ('X1 CS01', 'CS01 CS01 CS01 X1 S0', ['XCS']),
    'ax-X1-CS12=CS12-CS12-CS12-X1-S2': ('X1 CS12', 'CS12 CS12 CS12 X1 S2', ['XCS↓⁼']),
    'ax-X2-CS12=CS12-CS12-CS12-X2-S1': ('X2 CS12', 'CS12 CS12 CS12 X2 S1', ['XCS']),
    'ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01':
        ('CS01 H0 CS01 H0 S0', 'S0 H0 CS01 H0 CS01', ['CE↓⁼']),
    'ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01':
        ('CS01 H1 CS01 H1 S1', 'S1 H1 CS01 H1 CS01', ['CE']),
    'ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12':
        ('CS12 H1 CS12 H1 S1', 'S1 H1 CS12 H1 CS12', ['CE↓⁼']),
    'ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12':
        ('CS12 H2 CS12 H2 S2', 'S2 H2 CS12 H2 CS12', ['CE']),
    'ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12':
        ('CX10 CX01 CS12 CX01 CX10', 'CX12 CX21 CS01 CX21 CX12', ['E9⁼']),
    'ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12':
        ('CX10 CX01 CS12 CS12 CX01 CX10', 'CX01 CS12 CS12 CX01 CS12 CS12', [E11R]),
    'ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21':
        ('CS12 CX01 CS12 CS12 CS12 CX01', 'CS01 CX21 CS01 CS01 CS01 CX21', ['E10⁼']),
    'ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12':
        ('CS12 H1 CS12 H1 CS01 H1 CS01', 'CS01 H1 CS01 H1 CS12 H1 CS12', ['SH1']),
    'ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1':
        ('CS12 H1 CS12 CS12 CS12 H1 CS01 H1 CS12',
         'CS01 H1 CS01 CS01 CS01 H1 CS12 H1 CS01', ['E12⁼']),
}
for q in '012':
    VIA['ax-K%s-K%s=iI-iI-iI' % (q, q)] = ('H%s H%s' % (q, q), '', ['H2'])
    VIA['ax-S{0}-K{0}-S{0}-K{0}-S{0}-K{0}=iI-iI-iI'.format(q)] = (
        'S{0} H{0} S{0} H{0} S{0} H{0}'.format(q), 'w', ['E1⁼'])

for k, (l, r) in R.items():
    L, Rt = text(l), text(r)
    width = 3
    if k.startswith('ax-iI-') and k != 'ax-iI-iI-iI-iI=ε' or k in TRIV:
        lines = [(L, None), (Rt, [])]
    elif k in SIMPLE:
        lines = [(L, None), (Rt, SIMPLE[k])]
    elif k in VIA:
        a, b, e = VIA[k]
        lines = chain(L, Rt, a, b, e)
    else:
        raise SystemExit('no derivation for ' + k)
    D(NAME[k], width, lines, mirror=False)

# Lemma 19: the swap, encoded as (K0 K1 CZ)³ i³ and decoded.
SW = cs3.w('K0 K1 CS01 CS01') * 3 + ['iI'] * 3
D('Dσ⁼', 2, chain(text(SW), 'SW01', 'H0 H1 CS01 CS01 H0 H1 CS01 CS01 H0 H1 CS01 CS01',
                  'SW01', ['E13⁼']), mirror=False)

# Lemma 19: H, encoded as K and read with the ω the encoding dropped.
D('L19H⁼', 1, [('w wd H0', None), ('H0', ['w8'])], mirror=False)

# Only the new equations go into the module.
del OUT[:first]
