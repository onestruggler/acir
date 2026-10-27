import itertools, sys
from deriv import *
from q2 import matrix
def mono_words(m, maxlen=3):
    L = [Z(i) for i in range(m)] + [X(i, j) for i, j in itertools.combinations(range(m), 2)]
    for k in range(maxlen + 1):
        for w in itertools.product(L, repeat=k):
            yield tuple(w)
cases = {
 'ii': (2, [H(0,1), X(0,1)], X(0,1), H(0,1)),
 'iii': (3, [H(0,2), X(0,1)], X(0,1), H(1,2)),
 'iv': (3, [H(0,1), X(0,2)], X(0,2), H(1,2)),
 'v': (3, [H(1,2), X(0,2)], X(0,2), H(0,1)),
 'vi': (3, [H(1,2), X(0,1)], X(0,1), H(0,2)),
}
for name, (m, lhs, g, hb) in cases.items():
    target = matrix(lhs, m)
    for Y in mono_words(m):
        rhs = (g,) + Y + (hb,)
        if matrix(list(rhs), m) == target:
            eng = Engine(m)
            st = eng.search(tuple(lhs), rhs, maxd=8)
            print(name, fmt(Y), None if st is None else len(st))
            if st is not None:
                check_steps(st, lhs, rhs, eng)
                print("  ", lean_word(lhs), "->", lean_word(rhs))
                print("  ", lean_steps(st))
            break
