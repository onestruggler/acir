from auxeqs import *
import sys, pickle
TOPO = ['f1','f2','g','e9']
CITE = {
 '86': ['1','8','9'], '93': ['7','92'], '96': ['7','92','81','10','5','90'],
 '99': ['9','98','95','81','10'], '102': ['83','94','85','84'],
 '103': ['81','5','95','92','7','1'], '105': ['82','95','87'], '106': ['101','105'],
 '107': ['100','105','82'], '108': ['106','81','82'],
 '109': ['6','9','81','99','10','5','7'], '110': ['5','92','7','1','2','109','11','81'],
}
def base(name):
    n = name
    for suf in ('rs','r','s'):
        if n.endswith(suf) and not n[:-len(suf)].endswith('e'): n = n[:-len(suf)]; break
    return n
def allowed_set(lib, cites):
    want = set(TOPO)
    for c in cites:
        if c.isdigit() and int(c) <= 11: want |= {'e'+c, 'e'+c+'u'}
        elif c == '8': want.add('def8')
        else: want.add(c)
    return {n for (n,_,_) in lib.rules if base(n) in want or n in want}
def prove_all(LIM, only=None):
    lib = Lib()
    for n,l,r in BASE: add_variants(lib, n, l, r, 'axiom')
    fails = []
    for n,l,r in AUX:
        if only is not None and n not in only:
            st = search(l, r, lib, limit=LIM, maxins=6, slack=6)
        else:
            st = None
        if st is None and n in CITE:
            al = allowed_set(lib, CITE[n])
            t = time.time()
            st = search(l, r, lib, limit=LIM*4, maxins=8, slack=10, allowed=al)
            print(n, 'cited-search', 'FAILED' if st is None else len(st), round(time.time()-t,1), flush=True)
        elif st is not None:
            print(n, len(st), flush=True)
        if st is None: fails.append(n)
        else: assert run(l, lib.rules, st) == canon(r)
        add_variants(lib, n, l, r, st)
    print('fails', fails)
    return lib
if __name__ == '__main__':
    lib = prove_all(int(sys.argv[1]), only=set(CITE))
    pickle.dump(lib, open('lib3.pkl','wb'))
