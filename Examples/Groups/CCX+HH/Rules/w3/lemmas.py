"""The derivations of the three-wire relators of the tower, with their
lemmas, as data.

Re-runs the bootstrap of bootstrap.py, keeping for every identity that
closes its enumeration and the steps of its trace (a derivation of
identity ⟶ ε from that enumeration's facts), then keeps only the
lemmas the five tower relators need, transitively, and reports sizes.

    python3 -B lemmas.py [limit]
"""
import sys, time, pickle
sys.path.insert(0, '..')
import proofs as P
import partial as PT
import ptargets as TG
import bootstrap as B

ORDER = None   # filled from bootstrap.pkl: the order in which lemmas closed

class Derived:
    def __init__(self, name, text, tc, steps, lemmas_used):
        self.name, self.text, self.tc, self.steps = name, text, tc, steps
        self.lemmas_used = lemmas_used

def attempt(text, lemmas, limit):
    """lemmas: list of (name, gates).  Returns (tc, steps) or None."""
    rel = TG.gatesof(text)
    seeds = [rel[:i] for i in range(1, len(rel) + 1)]
    ax = PT.axioms() + [P.Axiom(('lemma', nm), l, ()) for nm, l in lemmas]
    tc = PT.PartialTC(len(PT.gs.names), ax, PT.MAC, seed=seeds, limit=limit)
    try:
        tc.run()
    except OverflowError:
        pass
    i, f, lab, st = tc.walk(0, rel)
    if i == len(rel) and tc.root(f) == 0 and lab == ():
        return tc, st
    return None

def closure(tc, steps):
    seen, stack = set(), [k for (_, (kind, k), _) in steps if kind == 'fact']
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        for (_, (kind, key), _) in tc.facts[f].steps:
            if kind == 'fact':
                stack.append(key)
    return seen

def used_lemmas(tc, steps, cl):
    out = set()
    for (_, (kind, k), _) in steps:
        if kind == 'ax' and tc.axioms[k].name[0] == 'lemma':
            out.add(tc.axioms[k].name[1])
    for f in cl:
        for (_, (kind, k), _) in tc.facts[f].steps:
            if kind == 'ax' and tc.axioms[k].name[0] == 'lemma':
                out.add(tc.axioms[k].name[1])
    return out

def run(limit_small=3000, limit_big=20000):
    order = pickle.load(open('bootstrap.pkl', 'rb'))
    lemmas, derived = [], {}
    t0 = time.time()
    for k, text in enumerate(order):
        name = f'L{k}'
        res = None
        for lim in (limit_small, limit_big):
            res = attempt(text, lemmas, lim)
            if res:
                break
        assert res, text
        tc, st = res
        cl = closure(tc, st)
        derived[name] = Derived(name, text, tc, st, used_lemmas(tc, st, cl))
        lemmas.append((name, TG.gatesof(text)))
        print(f'{name}: {text}  facts {len(cl)}  uses {sorted(derived[name].lemmas_used)}  '
              f'[{round(time.time() - t0)} s]', flush=True)
    return order, derived

if __name__ == '__main__':
    order, derived = run()
    targets = {TG.TARGETS[n]: n for n in ('A1', 'A2', 'A3')}
    need, stack = set(), [n for n, d in derived.items() if d.text in targets]
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        stack.extend(derived[n].lemmas_used)
    print('needed for A1-A3:', len(need), 'of', len(derived))
    print('facts:', sum(len(closure(derived[n].tc, derived[n].steps)) for n in need))
