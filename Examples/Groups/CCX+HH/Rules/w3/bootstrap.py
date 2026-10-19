"""Bootstrap derivations of three-wire identities.

Targets are tried in order by partial enumeration over the two-wire
group (partial.py).  A target that closes becomes an extra relator (a
lemma, with its derivation) for the later ones; the loop repeats until
no target is added.  Targets: the given tower relators, after every
short classical identity in X i, CX i, CCX0 spanning the three wires.

    python3 -B bootstrap.py [limit] [maxlen]
"""
import sys, time, itertools, pickle
sys.path.insert(0, '..')
import proofs as P
import partial as PT
import levels as Lv
import ptargets as TG

def short_identities(letters, maxlen):
    out, seen = [], set()
    for n in range(2, maxlen + 1):
        for word in itertools.product(letters, repeat=n):
            if any(word[i] == word[i + 1] for i in range(n - 1)) or word[0] == word[-1]:
                continue
            if Lv.ev(word) != Lv.rep.identity:
                continue
            ws = set()
            for x in word:
                ws |= Lv.WIRES[x]
            if ws != {0, 1, 2} or 'CCX0' not in word and len(word) < 4:
                continue
            key = min(min(word[i:] + word[:i], tuple(reversed(word[i:] + word[:i])))
                      for i in range(n))
            if key in seen:
                continue
            seen.add(key)
            out.append(' '.join(key))
    return out

def attempt(text, lemmas, limit):
    rel = TG.gatesof(text)
    seeds = [rel[:i] for i in range(1, len(rel) + 1)]
    ax = PT.axioms() + [P.Axiom(('lemma', k), l, ()) for k, l in enumerate(lemmas)]
    tc = PT.PartialTC(len(PT.gs.names), ax, PT.MAC, seed=seeds, limit=limit)
    try:
        tc.run()
    except OverflowError:
        pass
    i, f, lab, st = tc.walk(0, rel)
    return i == len(rel) and tc.root(f) == 0 and lab == ()

if __name__ == '__main__':
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    maxlen = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    classical = short_identities(['X0', 'X1', 'X2', 'CX0', 'CX1', 'CCX0'], maxlen)
    goals = [TG.TARGETS[n] for n in ('A1x', 'A2', 'A3', 'A1')]
    todo = classical + goals
    print('targets', len(todo), flush=True)
    lemmas, done = [], []
    progress = True
    t0 = time.time()
    while progress:
        progress = False
        for t in list(todo):
            if attempt(t, lemmas, limit):
                lemmas.append(TG.gatesof(t))
                done.append(t)
                todo.remove(t)
                progress = True
                print(f'  + {t}   [{len(done)} lemmas, {round(time.time() - t0)} s]', flush=True)
    print('derived', len(done), 'open', len(todo))
    for t in todo:
        print('  open:', t)
    pickle.dump(done, open('bootstrap.pkl', 'wb'))
