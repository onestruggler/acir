"""Run lemmas.py's bootstrap with D1 and D2 appended, keep the lemmas the
five tower relators need, and pickle everything emit_circuit.py uses.

    python3 -B lemmas_data.py
"""
import pickle, sys
import lemmas as LM
import ptargets as TG
import pipe as Pp

if __name__ == '__main__':
    order = pickle.load(open('bootstrap.pkl', 'rb'))
    order = order + [' '.join(Pp.THREE['D1']), ' '.join(Pp.THREE['D2'])]
    pickle.dump(order, open('bootstrap_d.pkl', 'wb'))
    LM_order = order
    lemmas, derived = [], {}
    for k, text in enumerate(LM_order):
        name = f'L{k}'
        res = None
        for lim in (3000, 20000, 60000):
            res = LM.attempt(text, lemmas, lim)
            if res:
                break
        assert res, text
        tc, st = res
        cl = LM.closure(tc, st)
        derived[name] = LM.Derived(name, text, tc, st, LM.used_lemmas(tc, st, cl))
        lemmas.append((name, TG.gatesof(text)))
        print(name, text, len(cl), sorted(derived[name].lemmas_used), flush=True)
    goals = {' '.join(Pp.THREE[n]): n for n in ('A1', 'A2', 'A3', 'D1', 'D2')}
    roots = {n: g for n, d in derived.items() for t, g in goals.items() if d.text == t}
    need, stack = set(), list(roots)
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        stack.extend(derived[n].lemmas_used)
    print('roots', roots, 'needed', len(need))
    data = {}
    for n in sorted(need, key=lambda s: int(s[1:])):
        d = derived[n]
        cl = sorted(LM.closure(d.tc, d.steps))
        facts = {f: (d.tc.facts[f].lhs, d.tc.facts[f].rhs, d.tc.facts[f].steps) for f in cl}
        axioms = [(a.name, a.lhs, a.rhs) for a in d.tc.axioms]
        data[n] = dict(text=d.text, gates=TG.gatesof(d.text), steps=d.steps, facts=facts,
                       axioms=axioms, uses=sorted(d.lemmas_used))
    pickle.dump(dict(lemmas=data, roots=roots), open('lemmas_data.pkl', 'wb'))
    print('facts total', sum(len(v['facts']) for v in data.values()))
