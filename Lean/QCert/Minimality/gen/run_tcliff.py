"""CliffT₂: Appendix D, the decoded Bian–Selinger relations (Appendix G.4) and the round trips
(Appendix F.4)."""
import sys, re, os, json, numpy as np
import tcliff as C
from tcliff import L, rep, mat, word
from driver import Driver
import figs

D = Driver(C)

# --- Bian and Selinger's two-qubit presentation (QCert.CliffordT2), letters on wires:
# qubit 0 is the top wire (wire 1), qubit 1 the bottom wire (wire 0).
def q(i): return 1 - i
def sH(i): return [L('H', q(i))]
def sS(i): return [L('S', q(i))]
def sT(i): return [L('T', q(i))]
CZ = [L('CZ')]
W = [L('w')]
def sX(i): return sH(i) + sS(i) + sS(i) + sH(i)
def sTdg(i): return sT(i) * 7
def sSdg(i): return sS(i) * 3
def sCX(i): return sH(i) + CZ + sH(i)
def opw(*fs):
    """Factors in the order of matrix multiplication, as a time-order word."""
    out = []
    for f in reversed(fs): out += f
    return out
def sCXw(i): return opw(sCX(i), sX(i))
def sCH(i): return opw(sS(i), sH(i), sT(i), sCX(i), sTdg(i), sH(i), sSdg(i))
def sCHw(i): return opw(sCH(i), sH(i))

def src_dec(w):
    """The decoding: ω, H, T as themselves, S ↦ T T, CZ ↦ H CNOT H on the bottom wire."""
    out = []
    for g, o in w:
        if g == 'w': out += [('w', 0)]
        elif g == 'H': out += [L('H', o)]
        elif g == 'T': out += [L('T', o)]
        elif g == 'S': out += [L('T', o), L('T', o)]
        elif g == 'CZ': out += [L('H', 0), L('CX', 0), L('H', 0)]
        else: raise Exception(g)
    return out

LOC = {'H': sH, 'S': sS, 'T': sT}
src = {}
for A in ['H₀', 'H₁', 'S₀', 'S₁', 'T₀', 'T₁', 'CZ']:
    a = CZ if A == 'CZ' else LOC[A[0]]({'₀': 0, '₁': 1}[A[1]])
    src['c1 .%s' % A] = (2, opw(W, a), opw(a, W))
for A in 'HST':
    for B in 'HST':
        src['c2 .%s .%s' % (A, B)] = (2, opw(LOC[A](0), LOC[B](1)), opw(LOC[B](1), LOC[A](0)))
src['c3'] = (2, W * 8, [])
for i in (0, 1):
    src['c4 %d' % i] = (2, sH(i) * 2, [])
    src['c5 %d' % i] = (2, sS(i) * 4, [])
    src['c6 %d' % i] = (2, opw(sS(i), sH(i)) * 3, W)
    src['c14 %d' % i] = (2, sT(i) * 2, sS(i))
    src['c15 %d' % i] = (2, opw(sT(i), sX(i)) * 2, W)
src['c7'] = (2, CZ * 2, [])
src['c8'] = (2, opw(sS(0), CZ), opw(CZ, sS(0)))
src['c9'] = (2, opw(sS(1), CZ), opw(CZ, sS(1)))
src['c10'] = (2, opw(sX(0), CZ), opw(CZ, sS(1), sS(1), sX(0)))
src['c11'] = (2, opw(sX(1), CZ), opw(CZ, sS(0), sS(0), sX(1)))
src['c12'] = (2, opw(CZ, sH(0), CZ), opw(sS(0), sH(0), CZ, sS(0), sH(0), sS(0), sS(1), W * 7))
src['c13'] = (2, opw(CZ, sH(1), CZ), opw(sS(1), sH(1), CZ, sS(1), sH(1), sS(1), sS(0), W * 7))
src['c16'] = (2, opw(sT(0), CZ), opw(CZ, sT(0)))
src['c17'] = (2, opw(sH(1), CZ, sH(0), sH(1), CZ, sH(0), sT(0)),
              opw(sT(1), sH(1), CZ, sH(0), sH(1), CZ, sH(0)))
src['c18'] = (2, opw(sCX(1), sT(1), sH(1), sTdg(1), sCXw(1), sT(1), sH(1), sTdg(1)),
              opw(sT(1), sH(1), sTdg(1), sCXw(1), sT(1), sH(1), sTdg(1), sCX(1)))
src['c19'] = (2, opw(sCX(1), sT(1), sH(1), sT(1), sH(1), sTdg(1), sCXw(1), sT(1), sH(1), sTdg(1), sH(1), sTdg(1)),
              opw(sT(1), sH(1), sT(1), sH(1), sTdg(1), sCXw(1), sT(1), sH(1), sTdg(1), sH(1), sTdg(1), sCX(1)))
src['c20'] = (2, opw(sCHw(1), sT(1), sCH(1), sCHw(0), sT(0), sCH(0)),
              opw(sCHw(0), sT(0), sCH(0), sCHw(1), sT(1), sCH(1)))
# the paper's labels of the relations (appendix_rules.tex)
PAPER = {'c5 %d': 't-C5', 'c6 %d': 't-C6', 'c7': 't-C7', 'c8': 't-C8', 'c9': 't-C9', 'c10': 't-C10',
         'c11': 't-C11', 'c12': 't-C12', 'c13': 't-C13', 'c14 %d': 't-C14', 'c16': 't-C16',
         'c17': 't-C17', 'c18': 't-C18', 'c19': 'old-t-C19', 'c20': 'old-t-C20'}

def check_src():
    for k, (n, l, r) in src.items():
        assert np.allclose(mat(n, src_dec(l)), mat(n, src_dec(r))), k

def dec_proofs():
    s = open(os.path.join(figs.SRC, 'appendix_decoding.tex'), encoding='utf-8').read()
    out = {}
    for m in re.finditer(r'Proof of the decoding of \\cref\{([^}]*)\}\](.*?)\\end\{proof\}', s, re.S):
        out[m.group(1)] = figs.tokens(m.group(2))
    return out

def from_proof(rel, toks, name=None):
    """D(L) = fig1 =(labels) fig2 = D(R)."""
    k, l, r = src[rel]
    dl, dr = src_dec(l[::-1]), src_dec(r[::-1])
    figs_ = [t[1] for t in toks if t[0] == 'fig']
    eqs = [t[1] for t in toks if t[0] == 'eq']
    f1, f2 = figs_[1], figs_[-2]
    labs = [e for e in eqs if e]
    labs = labs[0] if labs else []
    ways = [dl, word(f1)[1], word(f2)[1], dr]
    bound = ['t-H2', 't-Tpow8', 't-w8'] + (['CHup'] if rel == 'c20' else [])
    ways, labels = D.repair(rel, k, ways, [bound, labs, bound])
    return D.derive(name or ('dec' + rel), k, ways, labels)

# the encoding of the swap: CNOT, reversed CNOT, CNOT, with CNOT = H₁ CZ H₁
E_SWAP = sCX(1) + sCX(0) + sCX(1)

if __name__ == '__main__':
    only = sys.argv[1:]
    check_src()
    ders = figs.derivations(C.TEX)
    for lab in ders:
        if only and lab not in only and only != ['chains']: continue
        if lab == 't-HSTH':
            T0_ = L('T')
            D.derive('TCS', 2, [[T0_] + C._CSb, C._CSb + [T0_]],
                     [['t-phasegadgetCS', 't-phasegadget', 't-C', 't-CX2', 't-Tpow8', 'T6CS']])
            D.derive('T7CS', 2, [[T0_] * 7 + C._CSb, C._CSb + [T0_] * 7], [['T6CS', 'TCS']])
        if lab == 'lem:t-C19-dec-eq':
            T0_, T1_, X_ = L('T'), L('T', 1), L('CX')
            D.derive('T3CS', 2, [[T0_] * 3 + C._CSb, C._CSb + [T0_] * 3], [['TCS']])
            D.derive('CSdag', 2, [[T1_] * 7 + [T0_] * 7 + [X_, T0_, X_], C._CSb * 3],
                     [['t-CSCSCSCS', 't-Tpow8', 't-CX2', 't-C', 't-phasegadgetCS', 'T6CS']])
        if lab == 't-SCSd':
            D.derive('T6CS', 2, [C._T6 + C._CSb, C._CSb + C._T6],
                     [['t-phasegadgetCS', 't-phasegadget', 't-C', 't-CX2', 't-Tpow8']])
        D.from_chain(lab)
    if only == ['chains']: sys.exit(0)
    proofs = dec_proofs()
    # the controlled Hadamard of qubit 0, decoded, is the one of Figure 9 upside down
    T1_, H1_, H0_, X0_, SW_ = L('T', 1), L('H', 1), L('H'), L('CX'), L('SW')
    D.derive('CHup', 2, [[T1_, T1_, H1_, T1_, H1_, H0_, X0_, H0_, H1_] + [T1_] * 7 + [H1_] + [T1_] * 6,
                         [SW_] + C.CH_ + [SW_]], [['t-CNOTHH', 't-H2']])
    BOUND = ['t-H2', 't-Tpow8', 't-w8']
    direct = {'c3': ['t-w8'], 'c4': ['t-H2'], 'c5': ['t-Tpow8'], 'c14': [],
              'c15': ['t-TX', 't-X2', 't-Tpow8', 't-w8']}
    for key in src:
        nm = 'dec ' + key
        if only and key not in only and 'dec' not in only: continue
        k, l, r = src[key]
        dl, dr = src_dec(l[::-1]), src_dec(r[::-1])
        base = key.split(' ')[0]
        if base in ('c1', 'c2'):
            D.derive(nm, k, [dl, dr], [[]])
        elif base in direct:
            D.derive(nm, k, [dl, dr], [direct[base] + BOUND])
        elif base == 'c6':
            D.derive(nm, k, [dl, dr], [['lem:t-C6-dec-eq'] + BOUND])
        else:
            pl = PAPER[base]
            toks = proofs[pl]
            from_proof(key, toks, nm)
    # Appendix F.4: decoding the encoding of each generator
    if not only or 'DE' in only:
        GENS = {'w0': [('w', 0)], 'w1': [('w', 1)], 'w2': [('w', 2)], 'H0': [L('H')], 'H1': [L('H', 1)],
                'T0': [L('T')], 'T1': [L('T', 1)], 'CX': [L('CX')], 'SW': [L('SW')]}
        ENC = {'w0': W, 'w1': W, 'w2': W, 'H0': sH(1), 'H1': sH(0), 'T0': sT(1), 'T1': sT(0),
               'CX': sCX(1), 'SW': E_SWAP}
        for g in GENS:
            D.derive('DE ' + g, 2, [src_dec(ENC[g]), GENS[g]],
                     [['lem:t-dswap-unfolding', 't-CX2'] + BOUND if g == 'SW' else BOUND])
    # Greylyn's presentation in dimensions 2 and 1 (one wire and none)
    if not only or 'G' in only:
        gX = [L('H')] + [L('T')] * 4 + [L('H')]
        gH = [L('H')]
        gw0 = [L('T')] * 7 + [('w', 0)]
        gw1 = [L('T')]
        G1 = {'r1 0': (opw(*[gw0] * 8), []), 'r1 1': (opw(*[gw1] * 8), []),
              'r2': (opw(gH, gH), []), 'r3': (opw(gX, gX), []),
              'r4 01': (opw(gw0, gw1), opw(gw1, gw0)), 'r4 10': (opw(gw1, gw0), opw(gw0, gw1)),
              'r10': (opw(gX, gw1), opw(gw0, gX)), 'r11': (opw(gX, gw0), opw(gw1, gX)),
              'r16': (opw(gw0, gw1, gX), opw(gX, gw0, gw1)), 'r17': (opw(gw0, gw1, gH), opw(gH, gw0, gw1)),
              'r18': (opw(gH, gX), opw(gw1, gw1, gw1, gw1, gH)),
              'r19': (opw(gH, gw0, gw0, gH), opw(*([gw0] * 6 + [gH] + [gw0] * 3 + [gw1] * 5)))}
        GLAB = ['t-H2', 't-Tpow8', 't-w8', 't-E', 't-TX', 't-X2', 't-Z2', 't-HX', 't-XSX']
        for key, (l, r) in G1.items():
            assert np.allclose(mat(1, l), mat(1, r)), key
            D.derive('G1 ' + key, 1, [l, r], [GLAB])
        D.derive('G1DE w0', 1, [opw(gw0, gw1), [('w', 0)]], [GLAB])
        D.derive('G1DE w1', 1, [opw(gw0, gw1), [('w', 1)]], [GLAB])
        D.derive('G0 r1', 0, [[('w', 0)] * 8, []], [['t-w8']])
    print('PROOFS', sorted(proofs))
    print('REPAIRS', D.REPAIRS)
    print('FAILED', D.FAILED)
