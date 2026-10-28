"""Generate the W4 modules after A.lean: the equations of Lemma D.5 by solve2/proj.

    python gen_b.py D3.json OUTDIR

`SPEC` lists the equations in order; each follows the paper's chain (a row with three
diagrams first proves its first equality as `NNNa`), every step solved by solve2.Solver
with the known equations relabelled (`WS.rel_entry`), their inverses and their colour
exchanges (proved on demand, `proj.Project.realize`).  The theorems are written in
order, split into modules of about `CHUNK` runs (`B1.lean`, `B2.lean`, ...), only those
that the targets use; the exported equations get `eNNN : Derivable (theory 4) lNNN rNNN`.
"""
import json
import os
import sys
import time

sys.stdout.reconfigure(encoding='utf-8')
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import model  # noqa: E402
from gen_small import dec  # noqa: E402

import conv  # noqa: E402
import gen2  # noqa: E402
import proj  # noqa: E402
import solve2  # noqa: E402
import sym  # noqa: E402
import tok  # noqa: E402

NL = chr(10)
N = 4
M = 3
EXPORT = {157, 160, 168, 172, 173, 174, 209} | set(range(214, 249))


def avail4a(K, k):
    return k + sym.KIND_AR[K] <= 3 or (K == 'box' and k == 3) or (K == 'hg' and k == 2)


def make_project(log=print):
    P = proj.Project(N, avail4a, '(havail4a ih)', log=log)
    known = gen2.read_known(os.path.join(gen2.LEAN_DIR, 'A.lean'))
    for n, (L, R) in known.items():
        P.known(n, L, R)
    P.base = set(known)
    return P


def definitions(P):
    G = tok.G
    P.define(G('box', [0], [(3, 1), (2, 1), (1, 1)]), 'Dbox')
    P.define(G('zx', [0], [(3, 1), (2, 1), (1, 1)]), 'Dzx')
    P.define(G('xz', [0], [(3, 1), (2, 1), (1, 1)]), 'Dxz')
    P.define(G('hg', [0, 1], [(3, 1), (2, 1)]), 'Dhg')


def chain_seq(d, n, env=None):
    env = env or {}
    st = d['statements'][str(n)]
    L = gen2.diag_tokens(N, st[0], env)
    R = gen2.diag_tokens(N, st[-1], env)
    chains = [[gen2.diag_tokens(N, D, env) for D in ch['diags']] for ch in d['proofs'].get(str(n), [])]
    ws = gen2.full_chain(chains, L, R)
    seq = list(ws)
    if seq[0] != L:
        seq = [L] + seq
    if seq[-1] != R:
        seq = seq + [R]
    mid = gen2.diag_tokens(N, st[1], env) if len(st) == 3 else None
    return L, R, seq, mid


def prove_eq(P, d, n, budget=3000, env=None):
    L, R, seq, mid = chain_seq(d, n, env)
    if mid is not None and mid in seq:
        i = seq.index(mid)
        P.prove(f'{n}a', seq[:i + 1], budget)
    return P.prove(str(n), seq, budget)


# ----------------------------------------------------------------------------- endpoints

def endpoint(P, d, n, side, env=None):
    """Steps carrying the SmallDefs letters of a side to its token word."""
    env = env or {}
    st = d['statements'][str(n)]
    D = st[0] if side == 'l' else st[-1]
    S = P.solver([])
    letters, toks, steps = [], [], []
    for g0 in D['gates']:
        g = dec(g0)
        Lg = [('s',) + tuple(l) for l in model.word(N, [g], env)]
        Tg = conv.gate_tokens(N, g, env)
        pos = len(toks)
        if Lg == Tg:
            sub = []
        elif len(Tg) == 1 and Tg[0][0] == 'g' and [('s',) + tuple(l) for l in tok.letters(N, Tg[0])] == Lg:
            k, Lt = P.ctx.fold_entry(Tg[0])
            sub = [('rw', 0, k, False)]
        else:
            S.start(200)
            # The paper moves a distant two-wire gate with a short swap
            # network, while placeG uses a different network. Fold the
            # innermost conjugations first; the remaining comparison has
            # the gate's actual two-wire support.
            current = list(Lg)
            sub = []
            changed = True
            while changed:
                changed = False
                for i in range(len(current) - 2):
                    a, middle, b = current[i:i + 3]
                    if a == b and a[:2] == ('s', 'S'):
                        try:
                            local, _ = S.conj_tok(middle, a[2])
                        except solve2.Fail:
                            continue
                        local = solve2.shift(local, i)
                        current = S.run_words(current, local)
                        sub += local
                        changed = True
                        break
            sub += S.solve(current, Tg)
        steps += solve2.shift(sub, pos)
        letters += Lg
        toks += Tg
    return letters, toks, steps


def lean_endpoint(P, d, n, env=None, suffix=''):
    out = []
    ent = []
    nn = f'{n}{suffix}'
    for side in ('l', 'r'):
        letters, toks, steps = endpoint(P, d, n, side, env)
        e = P.compact(f'{side}{nn}', letters, toks, steps)
        nm = f'{side.upper()}C{nn}'
        lw = '[' + ', '.join(f'L.{t[1]} {t[2]}' for t in letters) + ']'
        out.append(f'def S{nm} : List Tk := ({lw} : List L).map Tk.s' + NL)
        tbl = '[' + (',' + NL + '  ').join(f'({tok.lean_word(x)}, {tok.lean_word(y)})'
                                           for x, y, _ in e.table) + ']'
        out.append(f'def T{nm} : Tbl := {tbl}' + NL)
        st = (',' + NL + '    ').join(tok.lean_step(s) for s in e.steps)
        tgt = f'{side.upper()}{nn}'
        out.append(f'theorem run{nm} : check 3 T{nm} S{nm} {tgt}' + NL + f'    [{st}] = true := by'
                   + NL + '  decide +kernel' + NL)
        allD = 'AllD.nil 4'
        for _, _, p in reversed(e.table):
            allD = f'AllD.cons ({p}) ({allD})'
        ent.append((nm, allD))
    (ln, la), (rn, ra) = ent
    out.append(NL.join([
        f'theorem e{nn} (ih : IH 4) : Derivable (theory 4) l{n} r{n} := by',
        f'  have hl : l{n} = wcT 4 S{ln} := circW_eq_wcT 4 _',
        f'  have hr : r{n} = wcT 4 S{rn} := circW_eq_wcT 4 _',
        '  rw [hl, hr]',
        f'  exact (check_sound ih ({la}) run{ln}).trans',
        f'    ((t{nn} ih).trans (check_sound ih ({ra}) run{rn}).symm)', '']))
    return NL.join(out)


# ----------------------------------------------------------------------------- output

HEADER = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.3 at width 4: {title}

Generated by `gen/sec8/w4/gen_b.py` from the paper's chains (parsed by
`gen/sec8/chains.py`): each equation as token words (`WE.Tk`), proved by a run of the
engine `WEng` decided by `decide +kernel`, its table entries the earlier equations
relabelled (`WS.rel_entry`), their inverses and colour exchanges (runs of their own),
Equation (81) (`WS.x81_entry`), swaps around a gate (`WS.swq_entry`).
-/
{imports}

namespace QCert.RealCliffordCH.Sec8.D.W4

open Circuit WE WS
open Eng (L)

'''


def used_names(P, targets):
    """The emitted theorems the targets need, transitively."""
    byname = {e.n: e for e in P.out}
    need = set()
    stack = list(targets)
    while stack:
        n = stack.pop()
        if n in need or n not in byname:
            continue
        need.add(n)
        for _, _, pf in byname[n].table:
            for m in byname:
                if f't{m} ih' in pf:
                    stack.append(m)
    return need


def write_modules(P, outdir, prefix, targets, extra, chunk, first_imports, title):
    need = used_names(P, targets)
    es = [e for e in P.out if e.n in need]
    mods = []
    cur = []
    for e in es:
        cur.append(e)
        if len(cur) >= chunk:
            mods.append(cur)
            cur = []
    if cur:
        mods.append(cur)
    names = []
    for i, ms in enumerate(mods):
        nm = f'{prefix}{i + 1}'
        imps = list(first_imports) if i == 0 else [f'import QCert.RealCliffordCH.Sec8.D.W4.{prefix}{i}']
        body = [gen2.lean_run(e, N, N) for e in ms]
        for e in ms:
            if e.n in extra:
                body.append(extra[e.n])
        text = HEADER.replace('{title}', f'{title} (part {i + 1})').replace('{imports}', NL.join(imps))
        text += NL.join(body) + NL + 'end QCert.RealCliffordCH.Sec8.D.W4' + NL
        with open(os.path.join(outdir, nm + '.lean'), 'w', encoding='utf-8', newline=NL) as f:
            f.write(text)
        names.append(nm)
    return names


def main():
    """gen_b.py D3.json OUTDIR MOD PREV EQ ...: solve EQ ... knowing A.lean and the modules
    PREV (comma separated, in order; '-' for none), write OUTDIR/MOD.lean importing the last."""
    d = json.load(open(sys.argv[1], encoding='utf-8'))
    outdir, mod, prev = sys.argv[2], sys.argv[3], sys.argv[4]
    eqs = [int(x) for x in sys.argv[5:]]
    P = make_project()
    prevs = [] if prev == '-' else prev.split(',')
    for pm in prevs:
        for n, (L, R) in gen2.read_known(os.path.join(gen2.LEAN_DIR, pm + '.lean')).items():
            P.known(n, L, R)
    if 'Dbox' not in P.ctx.eqs:
        definitions(P)
    done = []
    for n in eqs:
        t0 = time.time()
        try:
            prove_eq(P, d, n)
            done.append(n)
            print(f'({n}) OK {time.time() - t0:.1f}s', flush=True)
        except (solve2.Fail, AssertionError) as e:
            print(f'({n}) FAILED {str(e)[:300]}', flush=True)
    extra = {}
    for n in done:
        if n in EXPORT:
            extra[str(n)] = lean_endpoint(P, d, n)
    need = used_names(P, [str(n) for n in done])
    es = [e for e in P.out if e.n in need]
    imps = ['import QCert.RealCliffordCH.Sec8.D.W4.' + (prevs[-1] if prevs else 'Avail')]
    body = [gen2.lean_run(e, N, N) for e in es]
    for e in es:
        if e.n in extra:
            body.append(extra[e.n])
    text = HEADER.replace('{title}', f'equations {done[0]} to {done[-1]}' if done else 'nothing')
    text = text.replace('{imports}', NL.join(imps))
    text += NL.join(body) + NL + 'end QCert.RealCliffordCH.Sec8.D.W4' + NL
    with open(os.path.join(outdir, mod + '.lean'), 'w', encoding='utf-8', newline=NL) as f:
        f.write(text)
    print('wrote', mod, 'done', done, 'theorems', len(es))


if __name__ == '__main__':
    main()
