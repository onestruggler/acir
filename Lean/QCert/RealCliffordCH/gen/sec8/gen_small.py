"""Write Sec8/D/SmallDefs.lean, Sec8/D/Small.lean and the stubs W4.lean, W5.lean.

    python gen_small.py D2.json D3.json D4.json OUTDIR

The JSON files are dumps of chains.py (the parsed statements).  Every equation listed in
EQS is written as two circuits lNNN, rNNN : Circ K (engine words, `Eng.circW`), the
first and the last diagram of its row (for (148), whose row has three diagrams, l148a =
r148a and l148b = r148b), with a docstring in the paper's terms, the semantic equality
sNNN decided by `Fast.check`, and the statement eqNNN of PLAN.md through `small_of`.
Parametric families (a control of colour beta, a sign (-1)^a) take Bool parameters.
"""
import json
import os
import sys

import letters as LT
import model

D2 = list(range(117, 148)) + ['148a', '148b']
D3 = [157, 160, 168, 172, 173, 174, 209] + list(range(214, 249))
D4 = [267, 268]

SEM3 = False   # decide the three-wire statements in Lean as well (slow: see README)

OWNER = {}
for n in D2:
    OWNER[str(n)] = ('W3', 3)
for n in D3:
    OWNER[str(n)] = ('W4', 4)
for n in D4:
    OWNER[str(n)] = ('W5', 5)

PNAME = {'beta': 'β', 'a': 'a', 'b': 'b', 'alpha': 'α', 'gamma': 'γ', 'delta': 'δ'}


def dec(g):
    return tuple({int(k): v for k, v in p.items()} if isinstance(p, dict) else p for p in g)


def colstr(c):
    return {'b': '●', 'w': '○'}.get(c, PNAME.get(c, c))


def ctlstr(ctrls):
    return ','.join(f'{w}{colstr(c)}' for w, c in sorted(ctrls.items(), reverse=True))


def pretty(g):
    k = g[0]
    if k in ('Z', 'H', 'X'):
        return f'{k}{g[1]}'
    if k == 'Zw':
        return f'○{g[1]}'
    if k == 'SW':
        return f'SW{g[1]}{g[2]}'
    if k == 'PP':
        return f'P⊗P{g[1]}{g[2]}'
    if k == 'CZ':
        return f'CZ({ctlstr(g[1])})'
    if k == 'BOX':
        return f'Λ□(□{g[1]}|{ctlstr(g[2])})'
    if k == 'CHB':
        return f'ΛH(□{g[1]},H{g[2]}|{ctlstr(g[3])})'
    if k == 'CU':
        lab = g[1].replace('(-1)', '(-1)^')
        if not g[3]:
            return f'{lab}{g[2]}'
        return f'Λ{lab}({g[2]}|{ctlstr(g[3])})'
    return str(g)


def gate_segments(N, g):
    """The letters of a gate as segments: fixed words, or ('if', p, word if p, word if not p),
    a parametric control colour giving X on its wire on both sides when white, a sign
    (-1)^a choosing between ZX and XZ."""
    gp = model.params([g])
    if not gp:
        return [model.word(N, [g])]
    ctrls = next(p for p in g[1:] if isinstance(p, dict))
    xs = []
    for w, c in sorted(ctrls.items()):
        if c == 'w':
            xs.append(LT.xAt(w))
        elif c != 'b':
            xs.append(('if', c, [], LT.xAt(w)))
    black = tuple({w: 'b' for w in p} if isinstance(p, dict) else p for p in g)
    sign = model.params([black])
    if sign:
        assert len(sign) == 1, g
        a = sign[0]
        core = [('if', a, model.word(N, [black], {a: 1}), model.word(N, [black], {a: 0}))]
    else:
        core = [model.word(N, [black])]
    segs = xs + core + xs
    # check against the model for every value of the parameters
    for env in model.envs(gp):
        flat = []
        for sg in segs:
            flat += sg if isinstance(sg, list) else (sg[2] if env[sg[1]] else sg[3])
        assert flat == model.word(N, [g], env), (g, env)
    return segs


def lean_word(N, gates, ps):
    """A Lean expression of type List L for the gate list, with `if` on the parameters."""
    parts = []
    for g in gates:
        parts += gate_segments(N, g)
    merged = []
    for p in parts:
        if isinstance(p, list) and not p:
            continue
        if isinstance(p, list) and merged and isinstance(merged[-1], list):
            merged[-1] = merged[-1] + p
        else:
            merged.append(p)

    def show(p):
        if isinstance(p, list):
            return lw(p)
        return f'(if {PNAME.get(p[1], p[1])} then {show(p[2])} else {show(p[3])})'
    if not merged:
        return '[]'
    return ' ++ '.join(show(p) for p in merged)


def lw(w):
    return '[' + ', '.join(f'L.{a} {j}' for a, j in w) + ']'


def wrap(s, ind, width=100):
    """Break a long Lean expression at ', ' boundaries."""
    out, line = [], ind
    for tok in s.split(', '):
        add = tok if line.strip() == '' else ', ' + tok
        if len(line) + len(add) > width and line.strip():
            out.append(line + ',')
            line = ind + '  ' + tok
        else:
            line += add
    out.append(line)
    return '\n'.join(out)


def eqs_of(stmts):
    res = {}
    for k, ds in stmts.items():
        ds = [dict(nw=D['nw'], gates=[dec(g) for g in D['gates']]) for D in ds]
        if k == '148':
            res['148a'] = (ds[0], ds[1])
            res['148b'] = (ds[1], ds[2])
        else:
            res[k] = (ds[0], ds[-1])
    return res


def binders(ps):
    return ''.join(f'({PNAME.get(p, p)} : Bool) ' for p in ps)


def apps(ps):
    return ''.join(f' {PNAME.get(p, p)}' for p in ps)


def main():
    allst = {}
    for path in sys.argv[1:4]:
        allst.update(json.load(open(path, encoding='utf-8'))['statements'])
    out = sys.argv[4]
    eqs = eqs_of(allst)
    names = [str(n) for n in D2 + D3 + D4]
    missing = [n for n in names if n not in eqs]
    if missing:
        print('MISSING', missing)
    defs, small, stubs = [], [], {'W3': [], 'W4': [], 'W5': []}
    for n in names:
        if n not in eqs:
            continue
        L, R = eqs[n]
        K = L['nw']
        assert R['nw'] == K
        ok, env = model.equal(K, L['gates'], R['gates'])
        assert ok, (n, env)
        ps = sorted(set(model.params(L['gates'])) | set(model.params(R['gates'])))
        lex = lean_word(K, L['gates'], ps)
        rex = lean_word(K, R['gates'], ps)
        doc = (f'/-- ({n}), on {K} wires: `{" · ".join(pretty(g) for g in L["gates"]) or "1"}` = '
               f'`{" · ".join(pretty(g) for g in R["gates"]) or "1"}`. -/')
        defs.append(doc)
        defs.append(f'def l{n} {binders(ps)}: Circ {K} :=\n' + wrap(f'circW {K} ({lex})', '  '))
        defs.append('')
        defs.append(f'/-- The right-hand side of ({n}). -/')
        defs.append(f'def r{n} {binders(ps)}: Circ {K} :=\n' + wrap(f'circW {K} ({rex})', '  '))
        defs.append('')
        if K == 3 and SEM3:
            # the three-wire statements are also decided in Lean (cheap)
            if ps:
                cases = ' <;> '.join(f'cases {PNAME.get(p, p)}' for p in ps)
                defs.append(f'theorem s{n} {binders(ps)}: S.sem {K} (l{n}{apps(ps)}) = S.sem {K} (r{n}{apps(ps)}) := by\n'
                            f'  {cases} <;> exact Fast.sem_of_fast (by decide +kernel)')
            else:
                defs.append(f'theorem s{n} : S.sem {K} l{n} = S.sem {K} r{n} :=\n'
                            f'  Fast.sem_of_fast (by decide +kernel)')
            defs.append('')
        mod, _ = OWNER[n]
        stubs[mod].append(f'theorem d{n} {binders(ps)}(ih : IH {K}) :\n'
                          f'    Derivable (theory {K}) (l{n}{apps(ps)}) (r{n}{apps(ps)}) := by\n  sorry\n')
        small.append(f'/-- ({n}) on the bottom {K} wires of `m + {K}`. -/')
        small.append(f'theorem eq{n} {binders(ps)}(m : ℕ) (ih : IH (m + {K})) :\n'
                     f'    Derivable (theory (m + {K})) (Circuit.pad m (l{n}{apps(ps)})) (Circuit.pad m (r{n}{apps(ps)})) :=\n'
                     f'  small_of (sem_of_derivable (d{n}{apps(ps)} (ih.mono (by omega)))) (d{n}{apps(ps)}) m ih\n')
    hdr = '/-\nCopyright (c) 2026 QCert contributors. All rights reserved.\n\n'
    with open(os.path.join(out, 'SmallDefs.lean'), 'w', encoding='utf-8', newline='\n') as f:
        f.write(hdr + SMALLDEFS_DOC + '-/\nimport QCert.RealCliffordCH.Sec8.EngineN\n\n'
                'namespace QCert.RealCliffordCH.Sec8.D\n\nopen Circuit Eng\n\n')
        f.write('\n'.join(defs))
        f.write('\nend QCert.RealCliffordCH.Sec8.D\n')
    with open(os.path.join(out, 'Small.lean'), 'w', encoding='utf-8', newline='\n') as f:
        f.write(hdr + SMALL_DOC + '-/\nimport QCert.RealCliffordCH.Sec8.D.W3\nimport QCert.RealCliffordCH.Sec8.D.W4\n'
                'import QCert.RealCliffordCH.Sec8.D.W5\n\nnamespace QCert.RealCliffordCH.Sec8.D\n\nopen Circuit\n\n')
        f.write('\n'.join(small))
        f.write('\nend QCert.RealCliffordCH.Sec8.D\n')
    for mod, owner, doc in (('W4', '(ii)', W4_DOC), ('W5', '(iii)', W5_DOC)):
        path = os.path.join(out, mod + '.lean')
        with open(path, 'w', encoding='utf-8', newline='\n') as f:
            f.write(hdr + doc + '-/\nimport QCert.RealCliffordCH.Sec8.D.SmallDefs\n\n'
                    'namespace QCert.RealCliffordCH.Sec8.D\n\nopen Circuit\n\n')
            f.write('\n'.join(stubs[mod]))
            f.write('\nend QCert.RealCliffordCH.Sec8.D\n')
    if len(sys.argv) > 5:
        path = os.path.join(out, 'W3.lean')
        with open(path, 'w', encoding='utf-8', newline='\n') as f:
            f.write(hdr + W3_DOC + '-/\nimport QCert.RealCliffordCH.Sec8.D.SmallDefs\n\n'
                    'namespace QCert.RealCliffordCH.Sec8.D\n\nopen Circuit\n\n')
            f.write('\n'.join(stubs['W3']))
            f.write('\nend QCert.RealCliffordCH.Sec8.D\n')


SMALLDEFS_DOC = """
# Appendices D.2–D.4: the fixed-width equations (statements)

The auxiliary equations on 3, 4 and 5 qubits that the proofs of Lemmas 8.7
and 8.8 cite (`PLAN.md`): D.2 (117)–(147) and (148) (the two equalities of
its row, `148a` and `148b`); D.3 (157), (160), (168), (172)–(174), (209),
(214)–(248); D.4 (267), (268).  Each equation is a pair `lNNN rNNN : Circ K`
of engine words (`Eng.circW`: letters `H j`, `Z j`, `C j` = CZ, `K j` = CH,
`S j` = swap, in drawn order), with a docstring in the paper's terms:
`Z1` a black dot alone on wire 1, `○1` a white dot alone, `SW12` the swap, `P⊗P01`, `CZ(2●,0○)`,
`ΛZX(0|2●,1●)` the multi-controlled `ZX` with target wire 0, `Λ□(□0|…)`
the multi-controlled `Z` with box wire 0, `ΛH(□0,H1|…)` the
multi-controlled `H`; `●` black, `○` white, `β` a control of colour `β`
(true is black), `(-1)^aZX` is `ZX` for `a = false` and `XZ` otherwise.

Generated by `gen/sec8/gen_small.py` from the figures, parsed by
`gen/sec8/figparse.py`: every statement was checked numerically (both sides
denote the same operator, for every value of the parameters, in the model
`gen/sec8/mc.py` of `Syntax.lean`) before being written.  The semantic
equality that `Small.eqNNN` uses on wider circuits comes from the derivation
at width `K` (soundness), so nothing here is decided in Lean.

The gates are the canonical gates of Definition 2.4 (`box`, `zx`, `xz`,
`mch` of `Syntax.lean`, letter for letter), coloured by `X = H Z H` on both
sides of a white control (`colourW`), and placed as follows
(`gen/sec8/letters.py`, `place`): on wires `j, j + 1, …` in increasing
order, shifted; a two-wire gate on wires `lo < hi` that are not adjacent,
conjugated by the swaps `S lo, …, S (hi - 2)` carrying wire `lo` up next to
`hi` (as `cz20`, `ch20`), and one drawn upside down, conjugated by the swap
of its two wires; any other placement, by `MC.lean`'s network (`placeG`).
A controlled `X` is `H` on its target around a `CZ`.
"""

SMALL_DOC = """
# Appendices D.2–D.4: the fixed-width equations on wider circuits

`eqNNN m ih`: the equation `(NNN)` of `SmallDefs` on `K` wires, on the
bottom `K` wires of `m + K` wires, given completeness on fewer wires: by
Lemma 5.1 when `m ≥ 1` (`small_of`), by the derivation `dNNN` at width `K`
when `m = 0`.  The derivations are `W3` (package (i), D.2), `W4` (package
(ii), D.3) and `W5` (package (iii), D.4) of `PLAN.md`.
"""

W3_DOC = """
# Appendix D.2 at width 3 (package (i))

The equations (117)–(148) of `SmallDefs` derived on three wires from the
equations of Figure 4, with completeness on two wires (`IH 3`).
"""

W4_DOC = """
# Appendix D.3 at width 4 (package (ii)): statements

The equations of D.3 that the chain cites, at width 4, given completeness on
three wires (`IH 4`).  Owned by package (ii) of `PLAN.md`, which replaces each
`sorry` by its derivation.
"""

W5_DOC = """
# Appendix D.4 at width 5 (package (iii)): statements

The equations (267), (268) of D.4 at width 5, given completeness on four
wires (`IH 5`).  Owned by package (iii) of `PLAN.md`, which replaces each
`sorry` by its derivation.
"""

if __name__ == '__main__':
    main()
