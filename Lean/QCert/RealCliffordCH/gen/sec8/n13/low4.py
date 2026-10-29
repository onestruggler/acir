"""Four-wire cases of (339), (342), (344): engine runs over the D.3 equations.

    python low4.py 339|342|344        (from any directory; writes Sec8/D/N13/LowNNNW4.lean)

Uses the solver of gen/sec8/w4 (solve2, proj).  Every known equation of the W4 modules
enters the tables with its qualified proof.  The black cases are D.3 equations ((184),
(203), (204)); a white control on the `H` wire of the other gate is merged away
((170a), (166) for the box, `HgMerge` for the multi-controlled `H`), and the merged gate,
a two-wire gate with a dummy box wire, passes the other gate by a short chain through
Definition 2.4 (`P ⊗ P` around a box) and (155), (163).  The other colours come from
`derive_flip` (X on a wire, Equation (81) or (156), (207) on a box wire).
"""
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
W4 = HERE.parent / 'w4'
sys.path.insert(0, str(W4))
sys.path.insert(0, str(HERE.parent))
import gen2  # noqa: E402
import proj  # noqa: E402
import solve2  # noqa: E402
import sym  # noqa: E402
import tok  # noqa: E402

LEAN_W4 = Path(gen2.LEAN_DIR)
OUT_DIR = HERE.parent.parent.parent / 'Sec8' / 'D' / 'N13'

W4_MODS = ['A', 'B1', 'B2', 'B3', 'B4', 'Inverse', 'HgMerge', 'Expansion', 'Late', 'CommuteLate',
           'HgLate', 'SameRotation', 'WhiteCZ', 'ConjRotation', 'MergeZX', 'FullRotation',
           'ConjCommBase', 'ConjComm242', 'ConjComm243', 'ConjComm244', 'ConjComm245',
           'Opposite', 'AvailFull']
OTHER = [('BoxCommLow', 'W4Low'), ('BoxHgLow', 'W4LowHg')]


def log(s):
    print(s, flush=True)


def project():
    P = proj.Project(4, lambda k, n: n + sym.KIND_AR[k] <= 4, '(W4.havail4b ih)', log=log)
    for mod, ns in OTHER:
        p = LEAN_W4 / (mod + '.lean')
        for n, (l, r) in gen2.read_known(p).items():
            P.known(n, l, r, f'{ns}.t{n} ih')
    for mod in W4_MODS:
        p = LEAN_W4 / (mod + '.lean')
        if not p.exists():
            continue
        for n, (l, r) in gen2.read_known(p).items():
            P.known(n, l, r, f'W4.t{n} ih')
    return P


def chain(P, name, ws, names=()):
    for i, (u, v) in enumerate(zip(ws, ws[1:])):
        assert tok.weq(4, u, v), (name, i)
    steps = []
    for i, (u, v) in enumerate(zip(ws, ws[1:])):
        found = None
        for ns in [[], list(names), None]:
            S = P.solver(ns)
            S.start(400)
            t0 = time.time()
            try:
                found = S.solve(u, v)
                ok, bad = S.verify(u, v, found)
                assert ok, (name, i, bad)
                break
            except solve2.Fail:
                found = None
        if found is None:
            raise RuntimeError((name, i, u, v))
        log(f'  {name} step {i}: {len(found)} steps ({time.time() - t0:.1f} s)')
        steps += found
    return P.emit(name, ws[0], ws[-1], steps)


def flips(P, name, wires):
    ns = [name]
    for w in wires:
        for old in list(ns):
            new = old + 'f' + str(w)
            if new not in P.ctx.eqs:
                P.derive_flip(old, w, new)
            ns.append(new)
    return ns


G = tok.G
T, F = True, False
PPL = (('K', 0), ('H', 1), ('Z', 0), ('K', 0), ('H', 1), ('Z', 0), ('K', 0), ('H', 1), ('Z', 0),
       ('S', 0))


def pp(i, j):
    return ('p', 2, PPL, (i, j))


def P2(w, ps):
    return ('p', 2, tuple(w), tuple(ps))


def P1(w, q):
    return ('p', 1, tuple(w), (q,))


XL = (('H', 1), ('Z', 1), ('H', 1))


def run339(P):
    A1 = G('box', [0], [(3, T), (2, T), (1, T)])
    A0 = G('box', [0], [(3, T), (2, F), (1, T)])
    B = G('hg', [1, 2], [(3, F), (0, T)])
    Bin = G('box', [1], [(3, F), (2, T), (0, T)])
    Bin1 = G('box', [1], [(3, T), (2, T), (0, T)])
    C = P2([('C', 0)], [1, 3])
    CH = P2([('K', 0)], [1, 3])
    XCHX = P2(XL + (('K', 0),) + XL, [1, 3])
    H1 = P1([('H', 0)], 1)
    X3 = sym.XT(3)
    PP = pp(1, 2)
    chain(P, 'L339CB', [
        [C, B], [C, PP, Bin, PP], [PP, PP, C, PP, Bin, PP], [PP, CH, Bin, PP],
        [PP, H1, XCHX, Bin, PP], [PP, H1, Bin, XCHX, PP], [PP, H1, X3, Bin1, X3, XCHX, PP],
        [PP, X3, H1, Bin1, X3, XCHX, PP], [PP, X3, Bin1, H1, X3, XCHX, PP],
        [PP, X3, Bin1, X3, H1, XCHX, PP], [PP, Bin, H1, XCHX, PP], [PP, Bin, CH, PP],
        [PP, Bin, PP, PP, CH, PP], [B, C]], names=['155', '163'])
    chain(P, 'L339b1', [[A1, B], [B, A1]], names=['184'])
    chain(P, 'L339b0', [[A0, B], [A1, A1, A0, B], [A1, C, B], [A1, B, C], [B, A1, C],
                        [B, A1, A1, A0], [B, A0]], names=['166', '170a', '184', 'L339CB'])
    out = []
    for base in ['L339b1', 'L339b0']:
        out += flips(P, base, [0, 1, 3])
    return out


def run344(P):
    A1 = G('hg', [0, 1], [(3, T), (2, T)])
    A0 = G('hg', [0, 1], [(3, T), (2, F)])
    D = G('hg', [0, 1], [(3, T)])
    B = G('hg', [1, 2], [(3, F), (0, T)])
    Bin = G('box', [1], [(3, F), (2, T), (0, T)])
    CH = P2([('K', 0)], [1, 3])
    CZ = P2([('C', 0)], [1, 3])
    XCZX = P2(XL + (('C', 0),) + XL, [1, 3])
    Z1 = P1([('Z', 0)], 1)
    PP = pp(1, 2)
    chain(P, 'L344DB', [
        [D, B], [CH, B], [CH, PP, Bin, PP], [PP, PP, CH, PP, Bin, PP], [PP, CZ, Bin, PP],
        [PP, Z1, XCZX, Bin, PP], [PP, Z1, Bin, XCZX, PP], [PP, Bin, Z1, XCZX, PP],
        [PP, Bin, CZ, PP], [PP, Bin, PP, PP, CZ, PP], [B, CH], [B, D]], names=["159", "154"])
    chain(P, 'L344b1', [[A1, B], [B, A1]], names=['205', '204'])
    chain(P, 'L344b0', [[A0, B], [A1, A1, A0, B], [A1, D, B], [A1, B, D], [B, A1, D],
                        [B, A1, A1, A0], [B, A0]], names=['167', '171a', 'L344b1', 'L344DB'])
    out = []
    for base in ['L344b1', 'L344b0']:
        out += flips(P, base, [0, 3])
    return out


def run342(P):
    A1 = G('hg', [0, 1], [(3, T), (2, T)])
    A0 = G('hg', [0, 1], [(3, T), (2, F)])
    DA = G('hg', [0, 1], [(3, T)])
    B1 = G('hg', [0, 2], [(3, F), (1, T)])
    B0 = G('hg', [0, 2], [(3, F), (1, F)])
    DB = G('hg', [0, 2], [(3, F)])
    Bin = G('box', [0], [(3, F), (2, T), (1, T)])
    Ain = G('box', [0], [(3, T), (2, T), (1, T)])
    CH13 = P2([('K', 0)], [1, 3])
    CH23w = P2(XL + (('K', 0),) + XL, [2, 3])
    P02 = pp(0, 2)
    P01 = pp(0, 1)
    if '171af3' not in P.ctx.eqs:
        P.derive_flip('171a', 3, '171af3')
    if '167f3' not in P.ctx.eqs:
        P.derive_flip('167', 3, '167f3')
    chain(P, 'L342DA', [
        [DA, B1], [CH13, B1], [CH13, P02, Bin, P02], [P02, CH13, Bin, P02], [P02, Bin, CH13, P02],
        [P02, Bin, P02, CH13], [B1, CH13], [B1, DA]], names=['164'])
    chain(P, 'L342DB', [
        [A1, DB], [A1, CH23w], [P01, Ain, P01, CH23w], [P01, Ain, CH23w, P01],
        [P01, CH23w, Ain, P01], [CH23w, P01, Ain, P01], [CH23w, A1], [DB, A1]], names=['164'])
    chain(P, 'L342DD', [[DA, DB], [CH13, DB], [CH13, CH23w], [CH23w, CH13], [DB, CH13],
                        [DB, DA]])
    chain(P, 'L342b11', [[A1, B1], [B1, A1]], names=['203'])
    chain(P, 'L342b01', [[A0, B1], [A1, A1, A0, B1], [A1, DA, B1], [A1, B1, DA], [B1, A1, DA],
                         [B1, A1, A1, A0], [B1, A0]], names=['167', '171a', 'L342b11', 'L342DA'])
    chain(P, 'L342b10', [[A1, B0], [A1, B1, B1, B0], [A1, B1, DB], [B1, A1, DB], [B1, DB, A1],
                         [B1, B1, B0, A1], [B0, A1]],
          names=['167f3', '171af3', 'L342b11', 'L342DB'])
    chain(P, 'L342b00', [[A0, B0], [A0, B1, B1, B0], [A0, B1, DB], [B1, A0, DB],
                         [B1, A1, A1, A0, DB], [B1, A1, DA, DB], [B1, A1, DB, DA],
                         [B1, DB, A1, DA], [B1, DB, A1, A1, A0], [B1, DB, A0],
                         [B1, B1, B0, A0], [B0, A0]],
          names=['167', '171a', '167f3', '171af3', 'L342b01', 'L342DD', 'L342DB'])
    out = []
    for base in ['L342b11', 'L342b01', 'L342b10', 'L342b00']:
        out += flips(P, base, [3])
    return out


def iface_hg(P, names, num, tgB, wB):
    """The dispatch and interface theorems of (342) (`tgB = [0, 2]`, control of `B` on
    wire `wB = 1`) or (344) (`tgB = [1, 2]`, `wB = 0`)."""
    import itertools
    tgl = '[' + ', '.join(map(str, tgB)) + ']'
    out = [f'/-- ({num}) on four wires, every colour, the colourings differing on wire `3`. -/',
           f'theorem core{num}_4 (ih : IH 4) (a b c : Bool) :',
           '    Comm 4 (mc 4 .hg [0, 1] (SE.ctl 4 [(3, a), (2, b)] false))',
           f'      (mc 4 .hg {tgl} (SE.ctl 4 [(3, !a), ({wB}, c)] false)) := by',
           '  cases a <;> cases b <;> cases c']
    for a, b, c in itertools.product((False, True), repeat=3):
        A = G('hg', [0, 1], [(3, a), (2, b)])
        B = G('hg', tgB, [(3, not a), (wB, c)])
        out.append(f'  · exact t{find(P, names, [A, B])} ih')
    out += ['',
            f'/-- ({num}) on four wires, in the form of the interface `D.eq{num}`. -/',
            f'theorem eq{num}_4 (ih : IH 4) (x y : ℕ → Bool) (hxy : DiffOn 3 4 x y) (c₁ c₂ : Bool) :',
            '    Comm 4 (mc 4 .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 4 x)))',
            f'      (mc 4 .hg {tgl} (ctlOr (ctlAt {wB} c₂) (colOn 3 4 y))) := by',
            '  have hx : mc 4 .hg [0, 1] (ctlOr (ctlAt 2 c₁) (colOn 3 4 x)) =',
            '      mc 4 .hg [0, 1] (SE.ctl 4 [(3, x 3), (2, c₁)] false) := by',
            '    apply Net.mc_congr',
            '    intro i hi',
            '    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]',
            f'  have hy : mc 4 .hg {tgl} (ctlOr (ctlAt {wB} c₂) (colOn 3 4 y)) =',
            f'      mc 4 .hg {tgl} (SE.ctl 4 [(3, y 3), ({wB}, c₂)] false) := by',
            '    apply Net.mc_congr',
            '    intro i hi',
            '    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]',
            '  have h3 : y 3 = !x 3 := by',
            '    obtain ⟨i, hi, hiN, hne⟩ := hxy',
            '    obtain rfl : i = 3 := by omega',
            "    cases h : x 3 <;> cases h' : y 3 <;> simp_all",
            '  rw [hx, hy, h3]',
            f'  exact core{num}_4 ih (x 3) c₁ c₂', '']
    return '\n'.join(out)


def module_of(name):
    """The W4 module defining `t{name}`."""
    import re
    for f in sorted(LEAN_W4.glob('*.lean')):
        if re.search(r'^theorem t' + re.escape(name) + r' \(ih', f.read_text(encoding='utf-8'), re.M):
            return f.stem
    raise KeyError(name)


def imports_of(P):
    import re
    mods = {'AvailFull', 'BoxCommLow'}
    own = {str(e.n) for e in P.out}
    for e in P.out:
        for _, _, pf in e.table:
            for ns, n in re.findall(r'\b(W4|W4Low|W4LowHg)\.t(\w+) ih', pf):
                mods.add({'W4Low': 'BoxCommLow', 'W4LowHg': 'BoxHgLow'}.get(ns) or module_of(n))
            for n in re.findall(r'(?<![.\w])t(\w+) ih', pf):
                assert n in own, (e.n, pf)
    return sorted(mods)


def bool_lean(b):
    return 'true' if b else 'false'


def emit(P, num, title, iface):
    head = ['/-', 'Copyright (c) 2026 QCert contributors. All rights reserved.', '', title, '-/']
    head += [f'import QCert.RealCliffordCH.Sec8.D.W4.{m}' for m in imports_of(P)]
    head += ['import QCert.RealCliffordCH.Sec8.D.N13.Kit', 'import Mathlib.Tactic.IntervalCases', '',
             'set_option Elab.async false', '',
             f'namespace QCert.RealCliffordCH.Sec8.D.N13.L{num}W4', 'open Circuit WE WS Net',
             'open Eng (L)', 'open W4 (tH tZ tC tK tS tg tp)', 'set_option maxRecDepth 100000',
             'set_option maxHeartbeats 0', '']
    body = '\n'.join(gen2.lean_run(e, 4, 4) for e in P.out)
    txt = '\n'.join(head) + '\n' + body + '\n' + iface + f'\nend QCert.RealCliffordCH.Sec8.D.N13.L{num}W4\n'
    (OUT_DIR / f'Low{num}W4.lean').write_text(txt, encoding='utf-8', newline='\n')


def find(P, names, L):
    for n in names:
        if tuple(P.ctx.eqs[n][0]) == tuple(L):
            return n
    raise KeyError(L)


def iface339(P, names):
    out = ['/-- (339) on four wires, every colour, the colourings differing on wire `3`. -/',
           'theorem core339_4 (ih : IH 4) (a b c d : Bool) :',
           '    Comm 4 (mc 4 .box [0] (SE.ctl 4 [(3, a), (2, b), (1, c)] false))',
           '      (mc 4 .hg [1, 2] (SE.ctl 4 [(3, !a), (0, d)] false)) := by',
           '  cases a <;> cases b <;> cases c <;> cases d']
    import itertools
    for a, b, c, d in itertools.product((False, True), repeat=4):
        A = G('box', [0], [(3, a), (2, b), (1, c)])
        B = G('hg', [1, 2], [(3, not a), (0, d)])
        out.append(f'  · exact t{find(P, names, [A, B])} ih')
    out += ['',
            '/-- (339) on four wires, in the form of the interface `D.eq339`. -/',
            'theorem eq339_4 (ih : IH 4) (x y : ℕ → Bool) (hxy : DiffOn 3 4 x y) (c₁ c₂ c₃ : Bool) :',
            '    Comm 4 (mc 4 .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 4 x))))',
            '      (mc 4 .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 4 y))) := by',
            '  have hx : mc 4 .box [0] (ctlOr (ctlAt 2 c₁) (ctlOr (ctlAt 1 c₂) (colOn 3 4 x))) =',
            '      mc 4 .box [0] (SE.ctl 4 [(3, x 3), (2, c₁), (1, c₂)] false) := by',
            '    apply Net.mc_congr',
            '    intro i hi',
            '    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]',
            '  have hy : mc 4 .hg [1, 2] (ctlOr (ctlAt 0 c₃) (colOn 3 4 y)) =',
            '      mc 4 .hg [1, 2] (SE.ctl 4 [(3, y 3), (0, c₃)] false) := by',
            '    apply Net.mc_congr',
            '    intro i hi',
            '    interval_cases i <;> simp [colOn, ctlOr, ctlAt, SE.ctl, List.lookup_cons]',
            '  have h3 : y 3 = !x 3 := by',
            '    obtain ⟨i, hi, hiN, hne⟩ := hxy',
            '    obtain rfl : i = 3 := by omega',
            '    cases h : x 3 <;> cases h\' : y 3 <;> simp_all',
            '  rw [hx, hy, h3]',
            '  exact core339_4 ih (x 3) c₁ c₂ c₃', '']
    return '\n'.join(out)


if __name__ == '__main__':
    num = sys.argv[1]
    P = project()
    log(f'loaded {len(P.ctx.eqs)} equations')
    names = {'339': run339, '342': run342, '344': run344}[num](P)
    for n in names:
        L, R, _ = P.ctx.eqs[n]
        log(f'{n}: {tok.lean_word(L)} = {tok.lean_word(R)}')
    title = f'# ({num}) on four wires (generated by `gen/sec8/n13/low4.py {num}`)'
    iface = {'339': iface339,
             '342': lambda P, ns: iface_hg(P, ns, '342', [0, 2], 1),
             '344': lambda P, ns: iface_hg(P, ns, '344', [1, 2], 0)}[num](P, names)
    emit(P, num, title, iface)
    log(f'{len(P.out)} runs written')
