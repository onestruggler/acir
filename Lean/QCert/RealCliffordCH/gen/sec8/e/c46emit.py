"""Rule (46): solve the chain of `c46_chain.json` with the facts of `c46.py` and
write the Lean modules `E/Core46Facts.lean` and `E/Core46.lean`.

    python c46emit.py                 # solve and report
    python c46emit.py FACTS.lean MAIN.lean   # also write the modules
"""
import sys
from c46 import *


def canon_extra():
    return [('cpp', (), (P(0, 1), P(2, 3)), (P(2, 3), P(0, 1)))]


def all_facts2():
    facts = all_facts()
    for fam, prm, l, r in canon_extra():
        for s in PERMS:
            key = (frl(s, l), frl(s, r))
            if key not in facts: facts[key] = (fam, prm, tuple(s))
    return facts


ALWAYS = {'klein1', 'klein2', 'cpp'}


def step_fams(refs):
    f = fams_of(refs) | ALWAYS
    if '307' in refs or '313' in refs: f |= {'d112', 'd112i'}
    return f


def split_pp(w):
    """The gates other than P (x) P, and the P (x) P segments around them."""
    segs = [[]]; core = []
    for g in w:
        if g[0] == 'p': segs[-1].append(g)
        else: core.append(g); segs.append([])
    return core, [tuple(s) for s in segs]


def pp_segments(facts, allg, wa, wb):
    """When only the P (x) P between the other gates change, rewrite each segment."""
    ca, sa = split_pp(wa); cb, sb = split_pp(wb)
    if ca != cb or len(ca) == 0: return None
    idx = build_index(facts, allg, {'klein1', 'klein2', 'cpp', 'inv_pp'}, ALLPP)
    out = []; pos = 0
    for k, (x, y) in enumerate(zip(sa, sb)):
        p = bisearch(x, y, idx, depth=8)
        if p is None: return None
        out += [(pos + i, key, fwd) for (i, key, fwd) in p]
        pos += len(y) + (1 if k < len(ca) else 0)
    return out


def split_solve(wa, wb, solve):
    """Split at a common block whose two sides have the same non-P (x) P gates,
    and solve the two halves separately (the left one first)."""
    from collections import Counter

    def core(w): return Counter(g for g in w if g[0] != 'p')
    best = None
    for i in range(1, len(wa)):
        for j in range(1, len(wb)):
            L = 0
            while i + L < len(wa) and j + L < len(wb) and wa[i + L] == wb[j + L]: L += 1
            if L == 0: continue
            if core(wa[:i]) != core(wb[:j]): continue
            if best is None or L > best[2]: best = (i, j, L)
    if best is None: return solve(wa, wb)
    i, j, L = best
    left = split_solve(wa[:i], wb[:j], solve)
    right = split_solve(wa[i + L:], wb[j + L:], solve) if left is not None else None
    if left is None or right is None: return solve(wa, wb)
    return left + [(j + L + k, key, fwd) for (k, key, fwd) in right]


def solve2(facts, chain):
    allg = set(ALLPP)
    for (_, _, w) in chain: allg |= set(w)
    res = []
    for (n0, _, A), (n1, refs, B) in zip(chain, chain[1:]):
        if 'same' in refs:
            res.append((n1, refs, None, None, A, B)); continue
        off, wa, wb = window(A, B)
        ins = {g for g in set(wa) | set(wb) if wa.count(g) != wb.count(g)}
        if '111' in refs: ins |= ALLPP
        idx = build_index(facts, allg, step_fams(refs), ins)
        import time; t0 = time.time()
        path = pp_segments(facts, allg, wa, wb)
        if path is None:
            path = split_solve(wa, wb, lambda x, y: bisearch(x, y, idx))
        print('  solved', n1, refs, None if path is None else len(path), '%.1fs' % (time.time() - t0), flush=True)
        res.append((n1, refs, off, path, A, B))
    return res


# ---------------------------------------------------------------- Lean emission
def lb(b): return 'true' if b else 'false'
def lo(x): return 'none' if x is None else 'some ' + lb(x)


def lgd(g):
    if g[0] == 'p': return f'.p {g[1]} {g[2]}'
    _, K, tg, a = g
    return f'.g .{K} [{", ".join(map(str, tg))}] [{", ".join(lo(x) for x in a)}]'


def lword(w): return '[' + ', '.join(lgd(g) for g in w) + ']'


def canon_term(fam, prm):
    bs = ' '.join(lb(b) for b in prm)
    dec = ' (by decide)'
    return {
        'inv_box': f'k_inv_box ih {bs}', 'inv_hg': f'k_inv_hg ih {bs}', 'inv_pp': 'k_inv_pp ih',
        'c335': f'k335 ih {bs}', 'c336': f'k336 ih {bs}', 'c337': f'k337 ih {bs}{dec}',
        'c338': f'k338 ih {bs}', 'c339': f'k339 ih {bs}{dec}', 'c340': f'k340 ih {bs}',
        'c342': f'k342 ih {bs}{dec}', 'c344': f'k344 ih {bs}{dec}', 'c345': f'k345 ih {bs}',
        'mv274': f'k274 ih {bs}', 'mv277': f'k277 ih {bs}', 'd112': f'k112 ih {bs}',
        'd112i': f'k112i ih {bs}',
        'c308': f'k308 ih {bs}', 'klein1': 'k_klein1 ih', 'klein2': 'k_klein2 ih', 'cpp': 'k_cpp ih',
    }[fam]


def fact_proof(fam, prm, s):
    if fam == 'm309':
        t, a, w, b = prm
        a0 = list(a); a0[w] = None
        return (f'k309 ih {t} {w} [{", ".join(lo(x) for x in a0)}] {lb(b)} rfl (by decide) '
                f'(by decide) (by decide) rfl')
    if fam == 'm310':
        bw, hw, a, w, b = prm
        a0 = list(a); a0[w] = None
        return (f'k310 ih {bw} {hw} {w} [{", ".join(lo(x) for x in a0)}] {lb(b)} rfl (by decide)\n'
                f'    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl')
    return (f'fr_eq ih (σ := [{", ".join(map(str, s))}]) (by decide) (by decide) (by decide) (by decide)\n'
            f'    (by decide) ({canon_term(fam, prm)})')


def find_inv(facts, g):
    key = ((g, g), ())
    if key in facts: return key
    raise KeyError(g)


def wrap(s, width=96, ind='    '):
    out = []; line = ''
    for tok in s.split(' '):
        if len(line) + len(tok) + 1 > width and line:
            out.append(line); line = ind + tok
        else:
            line = (line + ' ' + tok) if line else tok
    out.append(line)
    return '\n'.join(out)


FACTS_HEAD = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (46): the facts of the chain

Generated by `gen/sec8/e/c46emit.py`: every equation the paper's chain for (46)
uses (pages 269-277), as an instance of a canonical equation of
`Core46Canon` moved by a frame (`fr_eq`), or a merge (309)/(310) at its
wires; each was checked numerically before being written.
-/
import QCert.RealCliffordCH.Sec8.E.Core46Canon

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.E.C46

open Circuit Net

section Facts

variable {n : ℕ} (ih : IH (n + 4))
include ih
'''

MAIN_HEAD = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (46): the chain

Generated by `gen/sec8/e/c46emit.py` (with `Core46Facts`) from the paper's chain (pages 269-277,
read off the vector drawings: `c46_chain.json`).  Words of gate descriptions,
the wires `0, ..., 3` explicit and white above:

* `W0`, the decoded right-hand side `B Cc Z F Dd Cc B A`, is rewritten (`ss1a`)
  to `g6 :: WIII` ((311), (337));
* `WIII` is rewritten to `WIV` (`ss1b`: from (III) to (IV));
* `g6 :: WIV` is rewritten to `g6 :: WIV.reverse` (`ss2`);
* the mirror of the second run: every gate is an involution, so `WIII = WIV`
  gives `WIII.reverse = WIV.reverse` (`rev_eq`);
* `g6 :: WIII.reverse` is rewritten to the decoded left-hand side `WEnd`
  (`ss3`).
-/
import QCert.RealCliffordCH.Sec8.E.Core46Facts

namespace QCert.RealCliffordCH.Sec8.E.C46

open Circuit Net
'''


def emit(facts, chain, sol, path_facts, path_main):
    names = [n for (n, _, _) in chain]
    i_III = names.index('p270d0'); i_IV = names.index('p274d2')
    i_m = names.index('p277d3'); i_m2 = names.index('p277d4')
    W = [w for (_, _, w) in chain]
    assert W[i_III][0] == W[i_IV][0] == W[i_m][0] == W[i_m2][0]
    III, IV = W[i_III][1:], W[i_IV][1:]
    assert W[i_m][1:] == tuple(reversed(IV)) and W[i_m2][1:] == tuple(reversed(III))
    used = []; uidx = {}

    def use(key):
        if key not in uidx: uidx[key] = len(used); used.append(key)
        return uidx[key]

    def steps(lo_, hi_, shift):
        out = []
        for (n1, refs, off, path, A, B) in sol[lo_:hi_]:
            assert path is not None, n1
            for (i, key, fwd) in path:
                assert off + i - shift >= 0
                out.append((off + i - shift, use(key), fwd))
        return out
    # sol[k] is the step from chain[k] to chain[k + 1]
    run1a = steps(0, i_III, 0)
    run1b = steps(i_III, i_IV, 1)
    run2 = steps(i_IV, i_m, 0)
    run3 = steps(i_m2, len(chain) - 1, 0)
    invs = sorted(set(III) | set(IV), key=lambda g: lgd(g))
    for g in invs: use(find_inv(facts, g))
    for key in used:
        assert sem_eq(key[0], key[1]), facts[key]
    L = [FACTS_HEAD]
    for k, key in enumerate(used):
        fam, prm, s = facts[key]
        L.append(f'/-- {fam} {prm} {"" if s is None else s} -/')
        L.append(f'theorem f{k} : Derivable (theory (n + 4))\n    (wI (n + 4) {wrap(lword(key[0]), 92, "      ")})\n'
                 f'    (wI (n + 4) {wrap(lword(key[1]), 92, "      ")}) := by\n  exact {fact_proof(fam, prm, s)}\n')
    L.append('end Facts\n')
    L.append('/-- The table of facts. -/')
    L.append('def T46 : List Eqn := [\n  ' + ',\n  '.join(f'({wrap(lword(a), 92, "    ")},\n    {wrap(lword(b), 92, "    ")})'
                                                      for (a, b) in used) + ']\n')
    L.append('theorem allT46 {n : ℕ} (ih : IH (n + 4)) : AllT (n + 4) T46 :=\n  ⟨' +
             wrap(', '.join(f'f{k} ih' for k in range(len(used))) + '⟩', 96, '    '))
    L.append('\nend QCert.RealCliffordCH.Sec8.E.C46\n')
    open(path_facts, 'w', encoding='utf-8', newline='\n').write('\n'.join(L))

    def ls(st): return '[' + ', '.join(f'({i}, {k}, {lb(f)})' for (i, k, f) in st) + ']'
    M = [MAIN_HEAD]
    M.append(f'def W0 : List GD := {wrap(lword(W[0]))}\n')
    M.append(f'def WIII : List GD := {wrap(lword(III))}\n')
    M.append(f'def WIV : List GD := {wrap(lword(IV))}\n')
    M.append(f'def WEnd : List GD := {wrap(lword(W[-1]))}\n')
    M.append(f'def g6 : GD := {lgd(W[i_III][0])}\n')
    M.append(f'def ss1a : List (ℕ × ℕ × Bool) := {wrap(ls(run1a))}\n')
    M.append(f'def ss1b : List (ℕ × ℕ × Bool) := {wrap(ls(run1b))}\n')
    M.append(f'def ss2 : List (ℕ × ℕ × Bool) := {wrap(ls(run2))}\n')
    M.append(f'def ss3 : List (ℕ × ℕ × Bool) := {wrap(ls(run3))}\n')
    for nm, word in (('III', III), ('IV', IV)):
        idxs = [uidx[find_inv(facts, g)] for g in word]
        M.append(f'theorem inv{nm} {{n : ℕ}} (ih : IH (n + 4)) :\n    W{nm}.Forall fun g => '
                 f'Derivable (theory (n + 4)) (wI (n + 4) [g, g]) (wI (n + 4) []) :=\n  ⟨' +
                 wrap(', '.join(f'f{k} ih' for k in idxs) + '⟩', 96, '    ') + '\n')
    M.append('end QCert.RealCliffordCH.Sec8.E.C46\n')
    open(path_main, 'w', encoding='utf-8', newline='\n').write('\n'.join(M))
    print('facts', len(used), 'steps', len(run1a), len(run1b), len(run2), len(run3))


if __name__ == '__main__':
    facts = all_facts2()
    print('facts', len(facts))
    chain = load_chain()
    sol = solve2(facts, chain)
    bad = False
    for (n1, refs, off, path, A, B) in sol:
        if path is None and off is not None:
            print(n1, refs, 'NOT FOUND'); bad = True
        elif path is not None:
            print(n1, refs, len(path), [facts[k][0] for (_, k, _) in path])
    if not bad and len(sys.argv) > 2:
        emit(facts, chain, sol, sys.argv[1], sys.argv[2])
