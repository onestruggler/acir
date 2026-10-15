"""Cliff₃'s derivations for completeness by transfer from Paper-V0
(Examples.Groups.ProjectiveClifford.Qupit.Paper-V0 at p = 3): the paper's
two-qutrit chains (its Appendix on qutrit Clifford circuits), Paper-V0's
rules decoded into Cliff₃ (cliff3v0.py) and derived up to a power of
ω₁₂, and the gates of Cliff₃ derived from the decodings of their
encodings.  Lines are in the notation of circ.gparse with cliff3's
spellings; the labels name each step's equations.

The one-wire rules are derived by Knuth–Bendix completion (kb.py) of
Cliff₃'s one-wire axioms, which present the group ⟨H, S, ω₁₂⟩ of order
2592; each rule of the completion is emitted as an equation derived
from the earlier ones, one rewrite a step.

The paper's chains are read from its LaTeX source by paper.py (with
$BLAKE_SRC the unpacked arXiv source; otherwise from the cache
cliff3paper.py that such a reading writes) and run by chains.py.

    python3 mkmod.py cliff3appendix Examples.Independence.Qutrit-Clifford.Derivations \\
        'TITLE' ../Qutrit-Clifford/Derivations.agda

writes the Agda module."""
import os
import sys
import cliff3
from cliff3 import LIB, OUT, derive, add_mirror, NATLABELS
import frag
import chains
import paper
from circ import parse
from kb import KB
import cliff3v0


PROBE = bool(os.environ.get('TPROBE'))      # report a failed derivation and go on


def D(name, width, lines, **kw):
    if not PROBE:
        return derive(name, width, lines, **kw)
    try:
        derive(name, width, lines, **kw)
    except SystemExit as e:
        print('PROBE-FAIL', name, str(e).splitlines()[0], flush=True)


def at(prefix):
    """The position of the letter after prefix."""
    return len(parse(prefix)) if prefix.strip() else 0


def direct(eq, prefix, fwd=True, shift=0):
    return ('direct', eq, at(prefix), fwd, shift)


MAIN = __name__ == '__main__'
MODE = sys.argv[1] if MAIN and len(sys.argv) > 1 else 'all'

# The swap moved the other way, and the scalar past the gates.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σS′⁼', 2, [('SW01 S0', None), ('S1 SW01', ['sS', 'ss'])])
NATLABELS += ['σH′⁼', 'σS′⁼']
for n in ['CPh⁼', 'KC⁼', 'CZ⁼', 'B⁼']:
    add_mirror(n)
D('Qwh⁼', 1, [('w H0', None), ('H0 w', [])], mirror=False)
D('Qws⁼', 1, [('w S0', None), ('S0 w', [])], mirror=False)


# ---------------------------------------------------------------------
# The paper's chains on two and three qutrits.  A label of the paper's
# names an axiom, a shortcut's definition (already spelled out: it
# cites nothing), or one of these chains, named after it.

RENAME = {'qt-omegapow12': 'w12', 'qt-hpow4': 'H4', 'qt-spow3': 'S3', 'qt-shpow3': 'E',
          'qt-ssprime': 'SS′', 'qt-cnotremove': 'CPh', 'qt-kcnot': 'KC', 'qt-czdecomp': 'CZ',
          'qt-swapdecomp': 'B', 'qt-I': 'I',
          'qt-K': None, 'qt-Sprime': None, 'qt-Z': None, 'qt-X': None, 'qt-Sdagger': None,
          'qt-H3': None}

CHAINS = ['qt-K2', 'qt-S-CNOT', 'qt-CKC', 'qt-KbCnot', 'qt-CCC', 'qt-SWAP', 'qt-PhGadget',
          'qt-CzRev', 'qt-SwCZ', 'qt-CComm', 'qt-CzComm']


def lname(l):
    return 'Q' + l[3:] + '⁼'


# K₀ conjugates CX₁₀ and CX₂₀ to their squares, one at a time.
FIX = {('qt-CComm', 5): [
    ('CX21 CX21 K0 CX10 CX10 CX21 CX20 K0', []),
    ('CX21 CX21 CX10 CX10 CX10 CX10 K0 CX21 CX20 K0', ['QKbCnot⁼']),
    ('CX21 CX21 CX10 K0 CX21 CX20 K0', ['QCCC⁼']),
    ('CX21 CX21 CX10 CX21 CX20 CX20 K0 K0', ['QKbCnot⁼'])]}

CH = chains.Chains('appendix_qutritclifford.tex', CHAINS, RENAME, 'cliff3paper.py', lname, FIX)
CH.run(D)


# ---------------------------------------------------------------------
# One wire: ⟨H, S, ω⟩ by Knuth–Bendix, letters w s h

FLET = {'w': 'w', 's': 'S0', 'h': 'H0'}
# (KB name, equation, shift, lhs, rhs): each equation as the library has it
F_AX = [('w12', 'ω¹²⁼', 0, 'w' * 12, ''), ('h4', 'H⁴⁼', 0, 'hhhh', ''), ('s3', 'S³⁼', 0, 'sss', ''),
        ('E', 'E⁼', 0, 'shs', 'hhhsshhhw'), ('SS′', 'SS′⁼', 0, 'shhshh', 'hhshhs'),
        ('wh', 'Qwh⁼', 0, 'wh', 'hw'), ('ws', 'Qws⁼', 0, 'ws', 'sw')]
F_AXD = {k: (e, s) for k, e, s, _, _ in F_AX}


def ftext(w):
    return ' '.join(FLET[x] for x in w)


def fword(t):
    out = ''
    for tok in t.split():
        if tok[0] == 'w':
            out += 'w' * (int(tok[1:]) if tok[1:] else 1)
        else:
            out += {'H0': 'h', 'S0': 's', 'K0': 'hh'}[tok]
    return out


def chain_lines(kb, ch, kbname):
    """A KB chain as lines of direct steps."""
    out = [(ftext(ch[0][0]), None)]
    for w, (k, p, fwd) in ch[1:]:
        l, r, pf, _ = kb.rules[k]
        if pf[0] == 'ax':
            eq, s = F_AXD[pf[1]]
            out.append((ftext(w), ('direct', eq, p, fwd == pf[2], s)))
        else:
            out.append((ftext(w), ('direct', kbname(k), p, fwd, 0)))
    return out


DEC = {name: (n, l, r) for name, n, l, r in cliff3v0.rules()}
XMG = cliff3v0.decode(cliff3v0.XMg)
C_XMG = cliff3v0.phase(XMG, 'K0', 1)

# The one-wire rules of Paper-V0, decoded (M-power at 1 is the same word
# on both sides), and the multiplier by g = -1 as ω^c K.
F_IDS = [('DV0-%s⁼' % name, fword(l), fword(r))
         for name, (n, l, r) in DEC.items() if n == 1 and name != 'M-power-1']
F_IDS.append(('DXMg⁼', fword(XMG), fword('w%d K0' % C_XMG)))


def f_kb():
    kb = KB('wsh', [(k, l, r) for k, _, _, l, r in F_AX], maxrules=20000)
    kb.complete(until=lambda: all(kb.prove(u, v) is not None for _, u, v in F_IDS), every=50)
    return kb


kb = f_kb()
kbname = lambda k: 'QKB%d⁼' % k
fchains = {name: kb.prove(u, v) for name, u, v in F_IDS}
for k in kb.needed(list(fchains.values())):
    ch = kb.rule_chain(k)
    if ch is not None:
        D(kbname(k), 1, chain_lines(kb, ch, kbname), mirror=False)
for name, u, v in F_IDS:
    D(name, 1, chain_lines(kb, fchains[name], kbname), mirror=False)


# ---------------------------------------------------------------------
# Two and three wires: Paper-V0's rules decoded

CZ0 = 'Hd0 CX10 H0'
CZ1 = 'Hd1 CX21 H1'
EX0 = cliff3v0.decode(cliff3v0.Ex)
EX1 = cliff3v0.decode(cliff3v0.up(cliff3v0.Ex))
CXd = cliff3v0.decode(cliff3v0.CX)
CXd1 = cliff3v0.decode(cliff3v0.up(cliff3v0.CX))
XMG1 = cliff3v0.decode(cliff3v0.up(cliff3v0.XMg))
K1 = 'w%d K1' % C_XMG


def rule(name):
    n, l, r = DEC[name]
    return n, l, r


# Lemma 19 for the gates: CNOT and the swap are the decodings of their
# encodings.
D('DCX⁼', 2, [('CX10', None), (CXd, ['H4'])], mirror=False)
D('DEx⁼', 2, [(EX0, None), ('H1 CX10 H0 H1 CX10 H0 H1 CX10 H0', ['H4']),
              ('SW01', ['QSwCZ⁼'])], mirror=False)

# CZ = H† CX H is CZ⁻¹ = H CX H† inverted: (CZ) read backwards.
D('CZinv⁼', 2, [('H0 CX10 CX10 Hd0', None),
                ('H0 CX10 CX10 Hd0 S1 Sd1', ['S3']),
                ('H0 CX10 CX10 Hd0 S1 S0 Sd0 Sd1', ['S3']),
                ('H0 CX10 CX10 Hd0 S1 S0 CX10 CX10 CX10 Sd0 Sd1', ['QCCC⁼']),
                ('H0 CX10 CX10 Hd0 S1 S0 CX10 Sd0 S0 CX10 CX10 Sd0 Sd1', ['S3']),
                ('H0 CX10 CX10 Hd0 S1 S0 CX10 Sd0 CX10 CX10 CX10 S0 CX10 CX10 Sd0 Sd1', ['QCCC⁼']),
                ('H0 CX10 CX10 Hd0 H0 CX10 Hd0 CX10 S0 CX10 CX10 Sd0 Sd1', ['CZ']),
                ('H0 CX10 CX10 CX10 Hd0 CX10 S0 CX10 CX10 Sd0 Sd1', ['H4']),
                ('CX10 S0 CX10 CX10 Sd0 Sd1', ['QCCC⁼', 'H4'])], mirror=False)


def two_three():
    n, l, r = rule('order-CZ')
    D('DV0-order-CZ⁼', n, [(l, None), ('Hd0 CX10 CX10 CX10 H0', ['H4']), (r, ['QCCC⁼', 'H4'])],
      mirror=False)
    n, l, r = rule('order-Ex')
    D('DV0-order-Ex⁼', n, [(l, None), ('SW01 ' + EX0, direct('DEx⁼', '')),
                          ('SW01 SW01', direct('DEx⁼', 'SW01')), (r, ['ss'])], mirror=False)
    n, l, r = rule('comm-CZ-S↑')
    D('DV0-comm-CZ-S↑⁼', n, [(l, None), (r, ['QS-CNOT⁼'])], mirror=False)
    n, l, r = rule('semi-M↑CZ')
    D('DV0-semi-M↑CZ⁼', n,
      [(l, None),
       ('%s %s %s' % (CZ0, CZ0, K1), direct('DXMg⁼', '%s %s' % (CZ0, CZ0), True, 1)),
       ('w%d Hd0 CX10 CX10 K1 H0' % C_XMG, ['H4']),
       ('%s %s' % (K1, CZ0), ['KC', 'H4']),
       (r, direct('DXMg⁼', '', False, 1))], mirror=False)
    for name, g in (('semi-Ex-S↑', 'S'), ('semi-Ex-H↑', 'H')):
        n, l, r = rule(name)
        D('DV0-%s⁼' % name, n,
          [(l, None), ('%s1 SW01' % g, direct('DEx⁼', '%s1' % g)),
           ('SW01 %s0' % g, ['σ%s′⁼' % g]), (r, direct('DEx⁼', '', False))], mirror=False)
    n, l, r = rule('blake-c12')
    D('DV0-blake-c12⁼', n,
      [(l, None), ('CX10 S0 %s %s S0 S0 S1 S1' % (CXd, CXd), direct('DCX⁼', '', False)),
       ('CX10 S0 CX10 %s S0 S0 S1 S1' % CXd, direct('DCX⁼', 'CX10 S0', False)),
       ('CX10 S0 CX10 CX10 S0 S0 S1 S1', direct('DCX⁼', 'CX10 S0 CX10', False)),
       ('H0 CX10 CX10 Hd0', ['CZinv⁼', 'S3']),
       ('H0 K0 CX10 K0 Hd0', ['QKbCnot⁼', 'H4']),
       (r, ['H4'])], mirror=False)
    n, l, r = rule('yang-baxter')
    D('DV0-yang-baxter⁼', n,
      [(l, None), ('SW12 %s %s' % (EX0, EX1), direct('DEx⁼', '', True, 1)),
       ('SW12 SW01 %s' % EX1, direct('DEx⁼', 'SW12')),
       ('SW12 SW01 SW12', direct('DEx⁼', 'SW12 SW01', True, 1)),
       ('SW01 SW12 SW01', ['sss']),
       ('%s SW12 SW01' % EX0, direct('DEx⁼', '', False)),
       ('%s %s SW01' % (EX0, EX1), direct('DEx⁼', EX0, False, 1)),
       (r, direct('DEx⁼', '%s %s' % (EX0, EX1), False))], mirror=False)
    n, l, r = rule('cz-slide')
    D('DV0-cz-slide⁼', n,
      [(l, None), ('%s SW12 %s' % (CZ0, EX0), direct('DEx⁼', CZ0, True, 1)),
       ('%s SW12 SW01' % CZ0, direct('DEx⁼', CZ0 + ' SW12')),
       ('SW12 SW01 %s' % CZ1, ['sH', 'sCX']),
       ('%s SW01 %s' % (EX1, CZ1), direct('DEx⁼', '', False, 1)),
       (r, direct('DEx⁼', EX1, False))], mirror=False)
    n, l, r = rule('semi-CX↑-CZ↓')
    mid = 'Hd0 CX10 H0 CX21 SW01 Hd1 CX21 H1 SW01'
    D('DV0-semi-CX↑-CZ↓⁼', n,
      [(l, None), ('CX21 ' + CZ0, ['H4']),
       ('Hd0 CX10 CX21 SW01 CX21 SW01 H0', ['I']),
       ('Hd0 CX10 H0 Hd0 CX21 SW01 CX21 SW01 H0', ['H4']),
       (mid, ['sH', 'σH′⁼']),
       ('Hd0 CX10 H0 %s SW01 %s SW01' % (CXd1, CZ1), ['H4']),
       ('Hd0 CX10 H0 %s %s %s SW01' % (CXd1, EX0, CZ1),
        direct('DEx⁼', 'Hd0 CX10 H0 %s' % CXd1, False)),
       (r, direct('DEx⁼', 'Hd0 CX10 H0 %s %s %s' % (CXd1, EX0, CZ1), False))], mirror=False)


two_three()
