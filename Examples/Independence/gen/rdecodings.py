"""G.2 of Blake's paper: Makary, Ross and Selinger's relations, decoded,
derived in RCliff₂.

The decoding reads a word of theirs (operator order) backwards and
spells CZ on wires a, a+1 as H_a CX(a+1, a) H_a (mrs.py), so that each
decoded relation is a drawing in time order.  (R1)–(R3) are axioms and
(R4)–(R12) are B.2–B.10 up to commuting letters (appendixB.py); the paper leaves
(R13)–(R16) to be mimicked from the Clifford ones, and they are derived
here: (R13) is (A.25) backwards; (R14) and (R15) come down, after the
H gates cancel and each decoded CZ next to a CNOT is absorbed by (CZr),
to identities of CNOT circuits; (R16) is (R15) with the wires reversed,
each decoded CZ turned round by B.1.  The decodings of CNOT and the
swap are as in Cliff₂.

Each equation is stated on the decoded letters exactly, so that the
Agda decoding function produces its sides."""
from appendixB import D, LIB, OUT
from frag import placed, nat
from circ import gwires, permute
from mrs import R, ARITY, D as decode, text

first = len(OUT)


def hcancel_steps(gs):
    """Delete pairs of H on one wire with nothing else on it between, one
    pair at a time: the circuits after each deletion."""
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


def down(word):
    """Lines from a decoded word to its H-cancelled form."""
    return [(text(c), ['H2']) for c in hcancel_steps(word)]


def up(word):
    """Lines from a decoded word's H-cancelled form back to it."""
    cs = [list(word)] + hcancel_steps(word)
    return [(text(c), ['H2']) for c in reversed(cs[:-1])]


CT = placed('A14⁼', [0])                # CX21 CX01 = CX01 CX21
CC0 = placed('A15⁼', [1, 0])            # CX01 CX02 = CX02 CX01
A13r = placed('A13⁼', [0, 1, 0])        # CX02 CX12 = CX01 CX12 CX01
CT2 = placed('A14⁼', [0, 1, 0])         # CX02 CX12 = CX12 CX02
n10 = nat(1, ('CX', 1, 0)).name         # SW12 CX10 = CX20 SW12
n21 = nat(1, ('CX', 2, 1)).name
n01 = nat(1, ('CX', 0, 1)).name

# (R4)–(R12): B.2–B.10, up to commuting letters.
CITE = {'R₄': 'B2⁼', 'R₅': 'B3⁼', 'R₆': 'B4⁼', 'R₇': 'B5⁼', 'R₈': 'B6⁼',
        'R₉': 'B7⁼', 'R₁₀': 'B8⁼', 'R₁₁': 'B9⁼', 'R₁₂': 'B10⁼'}
for k, lemma in CITE.items():
    l, r = R[k]
    D('D' + k + '⁼', ARITY[k], [(text(decode(l)), None), (text(decode(r)), [lemma])],
      mirror=False)

# (R13): (A.25) backwards.
l, r = R['R₁₃']
D('DR₁₃⁼', 3, [(text(decode(l)), None),
               ('H1 CX21 CX01 H1 H0 H0', ['CZr']),
               ('H0 H0 H1 CX21 CX01 H1', ['H2']),
               ('H0 H0 H1 CX01 CX21 H1', [CT]),
               (text(decode(r)), ['CZr'])], mirror=False)

# (R14): both sides are the CZ of wires 0 and 2.
l, r = R['R₁₄']
D('DR₁₄⁼', 3, [(text(decode(l)), None)] + down(decode(l)) + [
  ('CX10 CX01 H1 H0 CX21 CX10 H1 H0 CX10', ['CZr', 'H2']),
  ('CX10 CX01 H1 H0 CX21 H1 H0 CX01 CX10', ['CZr', 'H2']),
  ('CX10 CX01 H1 CX21 H1 CX01 CX10', ['H2']),
  ('SW01 CX10 H1 CX21 H1 CX10 SW01', ['B', 'CX2']),
  ('SW01 H1 CX21 H1 SW01', ['K1⁼', 'CX2']),
  ('H0 CX20 H0', ['sH']),
  ('SW12 H0 CX10 H0 SW12', [n10, 'ss']),
  ('CX12 CX21 CX12 H0 CX10 H0 CX12 CX21 CX12', ['B', 'CX2']),
  ('CX12 CX21 H0 CX10 H0 CX21 CX12', ['K2⁼', 'CX2']),
  ('H2 H1 CX21 H2 H1 CX21 H0 CX10 H0 CX21 H2 H1 CX21 H1 H2', ['CZr'])] +
  up(decode(r)), mirror=False)

# (R15): CX12 CX02 CX21 CX01 = CX01 CX12 CX21 between H1s.
l, r = R['R₁₅']
D('DR₁₅⁼', 3, [(text(decode(l)), None)] + down(decode(l)) + [
  ('H1 CX21 CX12 H1 H0 CX10 H1 CX21 H2 H1 CX21 H2 CX10 H0', ['CZr', 'H2']),
  ('H1 CX21 CX12 H1 H0 CX10 H1 CX21 CX12 H1 CX10 H0', ['CZr', 'H2']),
  ('H1 SW12 CX21 H1 H0 CX10 H1 SW12 CX21 H1 CX10 H0', ['B']),
  ('H1 SW12 CX21 CX01 H0 SW12 CX21 H1 CX10 H0', ['CZr', 'H2']),
  ('H1 SW12 CX21 CX01 SW12 CX21 CX01 H1', ['CZr', 'H2']),
  ('H1 CX12 CX02 CX21 CX01 H1', [n21, n01, 'ss']),
  ('H1 CX12 CX02 CX01 CX21 H1', [CT]),
  ('H1 CX12 CX01 CX02 CX21 H1', [CC0]),
  ('H1 CX01 CX01 CX12 CX01 CX02 CX21 H1', ['CX2']),
  ('H1 CX01 CX02 CX12 CX02 CX21 H1', [A13r]),
  ('H1 CX01 CX12 CX02 CX02 CX21 H1', [CT2]),
  ('H1 CX01 CX12 CX21 H1', ['CX2', 'ss']),
  ('H0 CX10 H0 H1 CX12 CX21 H1', ['B1⁼', 'H2']),
  ('H0 CX10 H0 H2 CX21 H2 H1 CX21 H1', ['A8c⁼', 'H2'])] +
  up(decode(r)), mirror=False)

# (R16): (R15) with the wires reversed, each decoded CZ turned round by
# B.1 on the way in and out.
rev = lambda w: 2 - w


def turned(word):
    """The circuits after turning the decoded CZs of a decoded word round,
    one at a time (each H_t CX(c, t) H_t, as the decoding writes it)."""
    cur = list(word)
    out = []
    i = 0
    while i + 2 < len(cur):
        h, x = cur[i], cur[i + 1]
        if h[0] == 'H' and x[0] == 'CX' and x[2] == h[1] and cur[i + 2] == h:
            c, t = x[1], x[2]
            cur = cur[:i] + [('H', c), ('CX', t, c), ('H', c)] + cur[i + 3:]
            out.append(list(cur))
            i += 3
        else:
            i += 1
    return out


l, r = R['R₁₆']
l15, r15 = R['R₁₅']
mr = [permute(g, rev) for g in decode(r15)]
bk = [decode(r)] + turned(decode(r))
D('DR₁₆⁼', 3, [(text(decode(l)), None)] +
  [(text(c), ['B1⁼']) for c in turned(decode(l))] +
  [(text(mr), [placed('DR₁₅⁼', [0, 1, 0])])] +
  [(text(c), ['B1⁼']) for c in reversed(bk[:-1])],
  mirror=False)

# CNOT: H CZ H on the target, decoded, is CNOT.
D('DCX⁼', 2, [('H0 H0 CX10 H0 H0', None), ('CX10', ['H2'])], mirror=False)

# The swap: H0 CZ H0 · H1 CZ H1 · H0 CZ H0, decoded, is σ.
D('Dσ⁼', 2, [('H0 H0 CX10 H0 H0 H1 H0 CX10 H0 H1 H0 H0 CX10 H0 H0', None),
             ('CX10 H1 H0 CX10 H0 H1 CX10', ['H2']),
             ('CX10 CX01 CX10', ['CZr', 'H2']),
             ('SW01 CX10 CX10', ['B']),
             ('SW01', ['CX2'])], mirror=False)

# Only the new equations go into the module.
del OUT[:first]
