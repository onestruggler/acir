"""Appendix A of Blake's paper: auxiliary derivations for Cliff₂.

Each derivation is the paper's chain of circuits, one line per string,
in time order, in the notation of circ.gparse (wire 0 at the bottom of
the paper's figures).  The labels are the paper's, widened where a step
also uses a mirrored lemma or hides a second rewrite; a few lines are
added where a step of the paper is too long for the search (marked as
such), and a few derivations take another route (said where).  (C14)
and (C15) are the decodings of Selinger's relations themselves
(selinger.py): (C15) is (C14) with the wires reversed.

Run as a script to write the Agda module (mkmod.py)."""
import sys, time
import cliff
from cliff import derive, add_mirror, placed, nat, LIB, OUT, emit
from selinger import C, D as decode, text
from circ import gwires, permute


def D(name, width, lines, **kw):
    derive(name, width, lines, **kw)

# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σS′⁼', 2, [('SW01 S0', None), ('S1 SW01', ['sS', 'ss'])])
for n in ['CPh⁼', 'B⁼', 'CZ⁼']:
    add_mirror(n)

# A.1–A.4: one wire.
D('A1⁼', 1, [('Z0 Z0', None), ('', ['S4'])])
D('A2⁼', 1, [('X0 X0', None), ('H0 Z0 Z0 H0', ['H2']), ('H0 H0', ['A1⁼']), ('', ['H2'])])
D('A3⁼', 1, [('X0 S0 X0', None),
             ('w H0 S0 S0 Sd0 H0 Sd0 S0 S0 H0', ['E']),
             ('w H0 S0 H0 S0 H0', ['S4']),
             ('w2 Sd0 H0 Sd0 S0 H0', ['E']),
             ('w2 Sd0', ['S4', 'H2'])])
D('A3d⁼', 1, [('X0 Sd0 X0', None),
              ('X0 S0 X0 X0 S0 X0 X0 S0 X0', ['A2⁼']),
              ('w6 Sd0 Sd0 Sd0', ['A3⁼']),
              ('w6 S0', ['S4'])])
D('A4⁼', 1, [('H0', None), ('H0 Sd0 S0', ['S4']), ('H0 Sd0 H0 H0 S0', ['H2']),
             ('wd S0 H0 S0 H0 S0', ['E'])])

# A.5: CNOT is an involution.
D('A5⁼', 2, [('CX10 CX10', None),
             ('CX10 CX10 S0 Sd0', ['S4']),
             ('CX10 CX10 CX01 S0 CX01 Sd0', ['CPh']),
             ('CX10 SW01 CX10 S0 CX01 Sd0', ['B']),
             ('CX10 CX01 SW01 S0 CX01 Sd0', []),
             ('SW01 CX10 SW01 S0 CX01 Sd0', ['B']),
             ('S0 Sd0', ['CPh']),
             ('', ['S4'])])

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

# A.13: a CNOT across a wire, as a commutator.
D('A13⁼', 3, [('CX20 CX10', None),
              ('CX21 CX10 CX10 CX21 CX20 CX10', ['A5⁼']),
              ('CX21 CX10 CX21 CX10 CX10', ['I']),
              ('CX21 CX10 CX21', ['A5⁼'])])

# A gate on the middle wire passes a CNOT between the outer two.
D('MH⁼', 3, [('H1 CX20', None), ('CX20 H1', ['sH'])])
D('MS⁼', 3, [('S1 CX20', None), ('CX20 S1', ['sS'])])
D('MHᵘ⁼', 3, [('H1 CX02', None), ('CX02 H1', ['sH', 'sCX', 'sss'])])
D('MSᵘ⁼', 3, [('S1 CX02', None), ('CX02 S1', ['sS', 'sCX', 'sss'])])
import cliff
cliff.SWAPS3 += ['MH⁼', 'MS⁼', 'MHᵘ⁼', 'MSᵘ⁼']

# A.14: two CNOTs with a common target commute.
D('A14⁼', 3, [('CX20 CX10', None),
              ('CX20 CX10 CX20 CX10 CX10 CX20', ['A5⁼']),
              ('CX21 CX10 CX21 CX21 CX10 CX21 CX10 CX20', ['A13⁼']),
              ('CX10 CX20', ['A5⁼'])])

# A.15: two CNOTs with a common control commute.
D('A15⁼', 3, [('CX20 CX21', None),
              ('H2 H1 H0 CX02 CX12 H2 H1 H0', ['A8⁼', 'H2']),
              ('H2 H1 H0 CX12 CX02 H2 H1 H0', [placed('A14⁼', [0, 1, 0])]),
              ('CX21 CX20', ['A8⁼', 'H2'])])

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

# A.25: (C12).
D('A25⁼', 3, [('H0 CX10 H0 H1 CX21 H1', None),
              ('H0 H0 H1 CX01 CX21 H1', ['A8⁼']),
              ('H0 H0 H1 CX21 CX01 H1', [placed('A14⁼', [0])]),
              ('H1 CX21 CX01 H1 H0 H0', ['H2']),
              ('H1 CX21 H1 H0 CX10 H0', ['A8⁼'])])

# H on a control: a corollary of A.8.
D('A8c⁼', 2, [('H1 CX10 H1', None), ('H0 CX01 H0', ['A8⁼', 'H2'])])

A14p = placed('A14⁼', [0])            # CX21 CX01 = CX01 CX21
n1 = nat(1, ('CX', 0, 1)).name         # SW12 CX01 = CX02 SW12

# A.26: (C13).
D('A26⁼', 3, [
  ('H1 CX21 H1 H2 H1 H1 CX21 H1 H1 H0 H0 CX10 H0 H1 H0 H1 CX21 H1 H2 H1 H1 CX21 H1', None),
  ('H1 CX21 H2 H1 CX21 CX10 CX21 H2 H1 CX21 H1', ['H2']),
  ('H1 CX21 CX12 H2 H1 CX10 H2 H1 CX12 CX21 H1', ['A8⁼', 'H2']),
  ('H1 CX21 CX12 H1 CX10 H1 CX12 CX21 H1', ['H2']),
  ('H1 CX21 CX12 H0 CX01 H0 CX12 CX21 H1', ['A8c⁼']),
  ('H1 SW12 CX21 H0 CX01 H0 CX21 SW12 H1', ['B']),
  ('H1 SW12 H0 CX01 H0 CX21 CX21 SW12 H1', [A14p]),
  ('H1 SW12 H0 CX01 H0 SW12 H1', ['A5⁼']),
  ('SW12 H0 CX01 H0 SW12', ['H2']),
  ('H0 CX02 H0', [n1]),
  ('H2 CX20 H2', ['A8c⁼']),
  ('H1 SW01 H2 CX21 H2 SW01 H1', ['H2']),
  ('H1 SW01 H2 CX21 H2 CX01 CX01 SW01 H1', ['A5⁼']),
  ('H1 SW01 CX01 H2 CX21 H2 CX01 SW01 H1', [A14p]),
  ('H1 CX01 CX10 H2 CX21 H2 CX10 CX01 H1', ['B']),
  ('H1 CX01 CX10 H0 H2 CX21 H2 H0 CX10 CX01 H1', ['H2']),
  ('H1 CX01 CX10 H1 H0 H1 H2 CX21 H2 H1 H1 H0 CX10 CX01 H1', ['H2']),
  ('H0 CX10 H0 H1 CX10 H1 H0 H1 H2 CX21 H2 H1 H1 H0 CX10 H1 H0 CX10 H0', ['A9⁼']),
  ('H0 CX10 H1 H0 CX10 H0 H1 H1 H2 CX21 H2 H1 H1 H0 CX10 H1 H0 CX10 H0', ['A8c⁼', 'A9⁼', 'H2']),
  ('H0 CX10 H0 H1 H0 H0 CX10 H0 H1 H1 H2 CX21 H2 H1 H1 H0 CX10 H0 H1 H0 H0 CX10 H0', ['H2']),
  ('H0 CX10 H0 H0 H1 H0 CX10 H0 H1 H2 H1 CX21 H1 H1 H2 H0 CX10 H0 H0 H1 H0 CX10 H0', ['H2'])])

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


# A.26 ends on D(C13)'s right side exactly.
# (appended below as a last H² step)

# A.27: (C14).
c14 = decode(C['C₁₄'][0])
D('A27⁼', 3, [
  (text(c14), None)] + [(text(c), ['H2']) for c in hcancel_steps(c14)] + [
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
  ('H2 H0 H2 H0', ['A5⁼']),
  ('', ['H2'])])

# A.28: (C15) is (C14) with the wires reversed, each decoded CZ turned
# round by A.9.
rev = lambda w: 2 - w
c15 = decode(C['C₁₅'][0])
target = [permute(g, rev) for g in c14]
lines = [(text(c15), None)]
cur = list(c15)
i = 0
while cur != target:
    # the first decoded CZ that differs: H_t CX(c,t) H_t -> H_c CX(t,c) H_c
    while cur[i] == target[i]:
        i += 1
    h, x = cur[i], cur[i + 1]
    assert h[0] == 'H' and x[0] == 'CX' and cur[i + 2] == h, (i, cur[i:i + 3])
    c, t = x[1], x[2]
    cur = cur[:i] + [('H', c), ('CX', t, c), ('H', c)] + cur[i + 3:]
    lines.append((text(cur), ['A9⁼']))
lines.append(('', [placed('A27⁼', [0, 1, 0])]))
D('A28⁼', 3, lines)
