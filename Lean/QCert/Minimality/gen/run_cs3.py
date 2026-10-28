"""CliffCS₂ on three wires: derivations of the decoded three-qubit relations (C12)–(C17) of Bian
and Selinger's presentation (the paper's Appendices E and G.5), read reversed as the paper draws
them.  Two-wire steps may be semantic: a two-wire lemma registered with `sem2` is proved in Lean
by the completeness of CliffCS₂ on two wires (`complete₂`), so only the three-wire structure ((I),
(SH_k), the lemma (C12) and the laws of the symmetry) is derived by rewriting.  Cached in
`cs3_cache.txt`.

    python3 run_cs3.py && python3 gen_cs3.py
"""
import sys, time, ast
import numpy as np
import cscliff as C
from cscliff import L
C.CACHE = 'cs3_cache.txt'
from driver import Driver
import figs
import cs3src as S

D = Driver(C)
try:
    old = ast.literal_eval(open('cscliff_cache.txt', encoding='utf-8').read())
    for k, v in old.items(): D.CACHE.setdefault(k, v)
except FileNotFoundError:
    pass

C5, C6, C7, C12 = 'lem:cs-C5-dec-eq', 'lem:cs-C6-dec-eq', 'lem:cs-C7-dec-eq', 'lem:cs-C12-dec-eq'

def chains():
    H0_, S0_, CS_, SW_, H1_ = L('H'), L('S'), L('CS'), L('SW'), L('H', 1)
    D.derive('CPh^', 2, [[CS_, S0_, CS_, CS_, CS_], [S0_]], [['cs-C', 'cs-CSrev']], quiet=True)
    D.derive('XCS^', 2, [[H0_, S0_, S0_, H0_, CS_], [CS_, CS_, CS_, H0_, S0_, S0_, H0_, L('S', 1)]],
             [['cs-XCS', 'cs-CSrev']], quiet=True)
    D.derive('CE^', 2, [[S0_, H0_, CS_, H0_, CS_], [CS_, H0_, CS_, H0_, S0_]], [['cs-SHCHC', 'cs-CSrev']],
             quiet=True)
    D.derive('RCX', 2, [[H1_, CS_, CS_, H1_], [SW_, H0_, CS_, CS_, H0_, SW_]], [['cs-CSrev']], quiet=True)
    C.SHORTCUTS.discard('cs-CNOT')
    C.LABELS['cs-CNOT'] = ['RCX']
    C.LABELS['cs-C'] = ['CPh', 'CPh^']
    C.LABELS['cs-XCS'] = ['XCS', 'XCS^']
    C.LABELS['cs-SHCHC'] = ['CE', 'CE^']
    for lab in [C5, C6, C7, C12, 'lem:cs-C17-dec-eq']:
        D.from_chain(lab)

SEM = {}
def sem2(name, l, r):
    """A two-wire lemma l = r (time order), proved in Lean through completeness on two wires;
    l and r must have the same matrix exactly."""
    assert np.allclose(C.mat(2, l), C.mat(2, r)), name
    SEM[name] = (list(l), list(r))
    D.lemmas[name] = (2, list(l), list(r))
    D.results[name] = (2, list(l), list(r), 'SEM', [])
    D.CACHE[name] = ('sem', D.results[name])

def ln(name, n, *ways, labs=None, each=None):
    for w in ways[1:]:
        assert np.allclose(C.mat(n, ways[0]), C.mat(n, w)), (name, w)
    t = time.time()
    labels = each if each is not None else [list(labs or [])] * (len(ways) - 1)
    ok = D.derive(name, n, [list(w) for w in ways], labels, quiet=True)
    print('  %s: %s (%.1fs)' % (name, 'ok' if ok else 'FAILED', time.time() - t), flush=True)
    return ok

def sh(w, p): return [(g, o + p) for (g, o) in w]
def rep(w, k): return list(w) * k

H0, H1, H2, S0, S1, CS0, CS1, SW0, SW1, W = (L('H'), L('H', 1), L('H', 2), L('S'), L('S', 1),
                                            L('CS'), L('CS', 1), L('SW'), L('SW', 1), L('w'))
# CNOTs (time order); control -> target on adjacent wires
CX10 = [H0, CS0, CS0, H0]          # c: control 1, target 0
CX01 = [H1, CS0, CS0, H1]          # e: control 0, target 1
CX21 = [H1, CS1, CS1, H1]          # b: control 2, target 1
CX12 = [H2, CS1, CS1, H2]          # a': control 1, target 2
CX20 = [SW0] + CX21 + [SW0]        # d: control 2, target 0 (Figure 9)
CZ0, CZ1 = [CS0, CS0], [CS1, CS1]
Z02 = [SW0] + CZ1 + [SW0]

def semantic_lemmas():
    two = lambda w: w            # words on wires 0, 1
    # two-wire facts on the pair 0, 1 (placed on 1, 2 as needed by the engine)
    A_, B_ = [H1, CS0, CS0, H1], [H0, CS0, CS0, H0]       # CX(0->1), CX(1->0) on two wires
    sem2('S2 cxcx', B_ + A_, [SW0] + B_)                 # [c, e] = [σ, c]
    sem2('S2 cxcx2', A_ + B_, B_ + [SW0])                # [e, c] = [c, σ]
    sem2('S2 cxcx3', A_ + B_, [SW0] + A_)                # [e, c] = [σ, e]
    sem2('S2 cxcx4', B_ + A_, A_ + [SW0])                # [c, e] = [e, σ]
    sem2('S2 cc', B_ + B_, [])
    sem2('S2 ee', A_ + A_, [])
    sem2('S2 czh', [CS0, CS0], [H0] + B_ + [H0])         # CZ = H₀ CX(1->0) H₀
    sem2('S2 czh1', [CS0, CS0], [H1] + A_ + [H1])        # CZ = H₁ CX(0->1) H₁
    sem2('S2 cz2', [CS0, CS0, CS0, CS0], [])
    sem2('S2 swc', [SW0] + B_ + [SW0], A_)              # the CNOT upside down
    sem2('S2 eh', A_ + [H1], [H1, CS0, CS0])            # CX(0->1) H₁ = H₁ CZ
    sem2('S2 he', [H1] + A_, [CS0, CS0, H1])

def three_lemmas():
    b, c, d = CX21, CX10, CX20
    # (I): [c, b, d] = [b, c]; with d d = 1 it gives d = b c b c and (b c)⁴ = 1, hence
    # b d = d b and b c b = c d
    ln('T3 dd', 3, d + d, [], labs=['S2 cc'])
    ln('T3 dbc', 3, d, b + b + d, b + c + c + b + d, b + c + b + c, each=[['S2 cc'], ['S2 cc'], ['I']])
    ln('T3 bc4', 3, b + c + b + c + b + c + b + c, d + b + c + b + c, d + d, [],
       each=[['T3 dbc'], ['T3 dbc'], ['T3 dd']])
    ln('T3 cb4', 3, c + b + c + b + c + b + c + b, b + b + c + b + c + b + c + b + c + b,
       b + b, [], each=[['S2 cc'], ['T3 bc4'], ['S2 cc']])
    ln('T3 bd', 3, b + d, b + b + c + b + c, c + b + c, c + b + c + c + b + c + b + c + b + c + b,
       b + c + b + c + b, d + b,
       each=[['T3 dbc'], ['S2 cc'], ['T3 cb4'], ['S2 cc'], ['T3 dbc']])
    ln('T3 bcb', 3, b + c + b, c + b + d + b, c + b + b + d, c + d,
       each=[['I'], ['T3 bd'], ['S2 cc']])
    # P3: CX(2->1) CZ(0,1) CX(2->1) = CZ(0,1) CZ(0,2)
    ln('T3 P3', 3, b + CZ0 + b, b + [H0] + c + [H0] + b, [H0] + b + c + b + [H0], [H0] + c + d + [H0],
       [H0] + c + [H0, H0] + d + [H0], CZ0 + [H0] + d + [H0], CZ0 + Z02,
       each=[['S2 czh'], [], ['T3 bcb'], ['H2'], ['S2 czh'], ['H2']])
    # a' = CX(1->2) passes CS(0,1), and c = CX(1->0) passes CS(1,2) (through (C12))
    ln('T3 aCS', 3, CX12 + [CS0], [CS0] + CX12, labs=[C12])
    ln('T3 cCS', 3, CX10 + [CS1], [CS1] + CX10, labs=[C12])
    ln('T3 aCZ', 3, CX12 + CZ0, CZ0 + CX12, labs=['T3 aCS'])
    ln('T3 Z02CZ', 3, Z02 + CZ0, CZ0 + Z02, labs=[C12, 'CSr'])
    ln('T3 cs02', 3, [CS0, SW0, CS1, SW0], [SW0, CS1, SW0, CS0], labs=[C12, 'CSr'])
    ln('T3 be', 3, CX21 + CX01, CX01 + CX21, labs=[C12, 'H2'])
    ln('T3 Z12', 3, [SW1, CS0, CS0, SW1, CS1], [CS1, SW1, CS0, CS0, SW1], labs=[C12, 'CSr'])
    # (P3) with the wires reversed: CX(0->1) CZ(1,2) CX(0->1) = CZ(1,2) CZ(0,2)
    ln('T3 Q', 3, CZ0 + b + CZ0, b + b + CZ0 + b + CZ0, b + CZ0 + Z02 + CZ0, b + CZ0 + CZ0 + Z02, b + Z02,
       each=[['S2 cc'], ['T3 P3'], ['T3 Z02CZ'], ['S2 cz2']])
    e = CX01
    ln('T3 P3r', 3, e + CZ1 + e, e + [H1] + b + [H1] + e, [H1] + CZ0 + b + CZ0 + [H1], [H1] + b + Z02 + [H1],
       [H1] + b + [H1] + Z02, CZ1 + Z02,
       each=[['S2 czh'], ['S2 eh', 'S2 he'], ['T3 Q'], ['H2'], ['S2 czh']])
    ln('T3 Z02CS1', 3, Z02 + [CS1], [SW1, CS0, CS0, SW1, CS1], [CS1, SW1, CS0, CS0, SW1], [CS1] + Z02,
       each=[['CSr'], ['T3 Z12'], ['CSr']])

def dec(w): return S.dec_rev(w)

def relations():
    R = S.rels()
    # (C12)
    l, r = R['c12']
    ln('R3 c12', 3, dec(l), dec(r), labs=[C12])
    a, b, c, e = CX12, CX21, CX10, CX01
    # (C13): both sides are CS(0,2), through the swaps
    l, r = R['c13']
    L0, R0 = dec(l), dec(r)
    ln('R3 c13', 3, L0, a + b + [CS0] + b + a, [SW1] + a + [CS0] + b + a, [SW1] + a + [CS0] + a + [SW1],
       [SW1, CS0] + a + a + [SW1], [SW1, CS0, SW1], [SW0, CS1, SW0], [SW0, CS1] + c + c + [SW0],
       [SW0] + c + [CS1] + c + [SW0], [SW0] + c + [CS1] + e + c, c + e + [CS1] + e + c, R0,
       each=[['ω8'], ['S2 cxcx3'], ['S2 cxcx4'], ['T3 aCS'], ['S2 ee'], ['CSr'],
             ['S2 cc'], ['T3 cCS'], ['S2 cxcx2'], ['S2 cxcx'], ['ω8']])
    # (C14): the paper's chain, its first step through (P3) and its last CNOTs respelled
    l, r = R['c14']
    L0, R0 = dec(l), dec(r)
    toks = figs.derivations(C.TEX)['lem:cs-C14-dec-eq']
    first, steps = figs.chain(toks)
    figw = [C.word(f)[1] for (_, f) in steps]
    labs = [list(lb) for (lb, _) in steps]
    # the step from C14-04 to C14-05 moves one CS₀₁ to the others through (C12)
    Zs = [SW0, CS1, SW0]
    A0 = figw[3]
    assert A0[:3] == [CS0] * 3 and A0[3:9] == Zs + Zs and A0[9:12] == [CS1] * 3 and A0[12] == CS0
    rest = A0[13:]
    extra = [[CS0] * 3 + Zs + Zs + [CS0] + [CS1] * 3 + rest, [CS0] * 4 + Zs + Zs + [CS1] * 3 + rest]
    ways = [L0, [CS0] + b + CZ0 + [CS0] + b, [CS0] + b + CZ0 + b + b + [CS0] + b,
            [CS0] + CZ0 + Z02 + b + [CS0] + b] + figw[:4] + extra + figw[4:5]
    # the step from C14-05 to C14-06: CX(2->1) and CX(0->1) commute
    f = [SW0] + c + [SW0]
    B0 = figw[4]
    pre = Zs + Zs + [CS1] * 3 + f + [CS1]
    assert B0 == pre + b + f + b and figw[5] == pre + f
    ways += [pre + b + e + b, pre + e + b + b, pre + e, figw[5]]
    # from C14-06 to the right side: (P3) with the wires reversed
    ways += [Z02 + [CS1] * 3 + e + [CS1] + e, [CS1] * 3 + Z02 + e + [CS1] + e,
             [CS1] + e + CZ1 + e + e + [CS1] + e, [CS1] + e + [CS1] * 3 + e, R0]
    each = ([['ω8'], ['S2 cc'], ['T3 P3'], []] + labs[1:4] + [[C12], ['T3 cs02'], [C5]] +
            [['S2 swc'], ['T3 be'], ['S2 cc'], ['S2 swc']] +
            [['S2 swc'], ['T3 Z02CS1'], ['T3 P3r'], ['S2 ee'], ['ω8']])
    ln('R3 c14', 3, *ways, each=each)
    # (C15)
    l, r = R['c15']
    L0, R0 = dec(l), dec(r)
    ln('R3 c15', 3, L0, a + b + CZ0 + b + a, [SW1] + a + CZ0 + b + a, [SW1] + a + CZ0 + a + [SW1],
       [SW1] + CZ0 + a + a + [SW1], [SW1] + CZ0 + [SW1], [SW0] + CZ1 + [SW0], CZ0 + CZ0 + Z02,
       CZ0 + Z02 + CZ0, b + CZ0 + b + CZ0, R0,
       each=[['ω8'], ['S2 cxcx3'], ['S2 cxcx4'], ['T3 aCZ'], ['S2 ee'], ['CSr'],
             ['S2 cz2'], ['T3 Z02CZ'], ['T3 P3'], ['ω8']])
    # (C16): (SH₁)
    l, r = R['c16']
    ln('R3 c16', 3, dec(l), dec(r), labs=['SH 1', 'ω8'])
    # (C17): the paper's chain
    l, r = R['c17']
    ln('R3 c17', 3, dec(l), dec(r), labs=['lem:cs-C17-dec-eq', 'ω8'])

if __name__ == '__main__':
    chains()
    semantic_lemmas()
    three_lemmas()
    relations()
    print('FAILED', D.FAILED)
