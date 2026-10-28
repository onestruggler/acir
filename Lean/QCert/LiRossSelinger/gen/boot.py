"""Bootstrap derived relations on Fin 4 (macros from earlier ones), with waypoints."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import time, sys, json
from rules import *
from bfs import Engine, apply_steps
from macros import BASE, macro_instances
from chain import chain
k = K(0, 1, 2, 3)
WAY = {
 'k31': [
   (N(1), N(2), k),
   (N(2), X(1, 3), N(3), X(1, 3), k),
   (N(2), X(1, 3), N(3), k, X(2, 3)),
   (X(1, 3), N(2), N(3), k, X(2, 3)),
   (X(1, 3), k, X(0, 2), X(1, 3), X(2, 3)),
   (k, X(2, 3), X(0, 2), X(1, 3), X(2, 3)),
   (k, X(0, 3), X(1, 2))],
 'relk4': [
   (N(0), N(1), N(2), N(3), k),
   (N(0), N(1), k, X(0, 2), X(1, 3)),
   (X(0, 2), X(1, 3), N(2), N(3), X(0, 2), X(1, 3), k, X(0, 2), X(1, 3)),
   (X(0, 2), X(1, 3), N(2), N(3), k, N(2), N(3), X(0, 2), X(1, 3)),
   (X(0, 2), X(1, 3), k, X(0, 2), X(1, 3), N(2), N(3), X(0, 2), X(1, 3)),
   (X(0, 2), X(1, 3), k, N(0), N(1)),
   (k, N(0), N(1), N(2), N(3))],
 'k22': [
   (N(0), N(2), k),
   (N(1), N(3), N(0), N(1), N(2), N(3), k),
   (N(1), N(3), k, N(0), N(1), N(2), N(3)),
   (k, X(0, 1), X(2, 3), N(0), N(1), N(2), N(3))],
 'k12': [
   (N(0), N(1), k),
   (N(2), N(3), N(0), N(1), N(2), N(3), k),
   (N(2), N(3), k, N(0), N(1), N(2), N(3)),
   (k, X(0, 2), X(1, 3), N(0), N(1), N(2), N(3))],
 'k32': [
   (N(0), N(3), k),
   (N(1), N(2), N(0), N(1), N(2), N(3), k),
   (N(1), N(2), k, N(0), N(1), N(2), N(3)),
   (k, X(0, 3), X(1, 2), N(0), N(1), N(2), N(3))],
}
order = ['ksym2', 'ksym6', 'ksym4', 'ksym5', 'k21', 'k11', 'k31', 'relk4', 'k12', 'k22', 'k32']
done = []
res = {}
for nm in order:
    kk, l, r = BASE[nm]
    mac = macro_instances(done, 4)
    E = Engine(4, macros=mac)
    lines = WAY.get(nm, [l, r])
    assert tuple(lines[0]) == l and tuple(lines[-1]) == r
    print(nm); sys.stdout.flush()
    st, bad = chain(E, lines, mac, extras=(2, 3, 4, 5, 6), depth=16)
    if st is None:
        print('FAILED', nm, 'gap', bad); break
    assert apply_steps(l, st, mac) == tuple(r)
    res[nm] = st
    done.append(nm)
# K (-1)_a K from (4b), with the derived relations as macros
nm = 'knk0'
kk, l, r = BASE[nm]
mac = macro_instances(done, 4)
E = Engine(4, macros=mac)
st = None
for extra in (2, 3, 4, 5):
    st = E.search(l, r, depth=18, maxlen=max(len(l), len(r)) + extra, ins_letters=set(l) | set(r),
                  limit=3_000_000)
    print(nm, extra, None if st is None else len(st)); sys.stdout.flush()
    if st: break
assert apply_steps(l, st, mac) == tuple(r)
res[nm] = st
json.dump(res, open(os.path.join(HERE, 'boot.json'), 'w'))
print('done', done)
