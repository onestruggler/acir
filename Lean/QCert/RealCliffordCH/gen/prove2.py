from chains import *
from ordered import CITE, allowed_set
import sys, pickle
def prove_chain(lib, ch, LIM):
    steps = []
    for i in range(len(ch)-1):
        st = search(ch[i], ch[i+1], lib, limit=LIM, maxins=6, slack=6)
        if st is None:
            st = search(ch[i], ch[i+1], lib, limit=LIM*3, maxins=8, slack=10)
        if st is None: return None, i
        steps += st
    return steps, None
def main(LIM):
    lib = Lib()
    for n,l,r in BASE: add_variants(lib, n, l, r, 'axiom')
    order = []
    for n,l,r in AUX:
        if n == '110': order += ONEW
        order += EXTRA_BEFORE.get(n, [])
        order.append((n,l,r))
    fails = []
    for n,l,r in order:
        t = time.time()
        if n in CHAINS:
            st, bad = prove_chain(lib, CHAINS[n], LIM)
            if st is None: print(n, 'chain FAILED at segment', bad, round(time.time()-t,1), flush=True)
        elif n.startswith('L71'):
            sub = Lib(); sub.rules = [x for x in lib.rules if x[0] in ('e1u','e2u','e3u')]
            st = search(l, r, sub, limit=LIM*5, maxins=16, slack=18)
            if st is not None:
                # reindex steps to lib.rules
                st = [(u, v, lib.idx(sub.rules[k][0]), d) for (u,v,k,d) in st]
        else:
            st = search(l, r, lib, limit=LIM, maxins=6, slack=6)
            if st is None and n in CITE:
                st = search(l, r, lib, limit=LIM*4, maxins=8, slack=10, allowed=allowed_set(lib, CITE[n]))
        if st is None: fails.append(n); print(n, 'FAILED', flush=True)
        else:
            assert run(l, lib.rules, st) == canon(r), n
            print(n, len(st), 'steps', round(time.time()-t,1), flush=True)
        add_variants(lib, n, l, r, st)
    print('fails', fails, 'rules', len(lib.rules))
    pickle.dump(lib, open('lib4.pkl','wb'))
if __name__ == "__main__": main(int(sys.argv[1]))
