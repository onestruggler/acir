"""Pushing a block of letters through a word, on three wires (for w3.py).

A block B (a list of letters: P (x) P, the cycle S0 S1, ...) moves right across a letter x
(x B' = ... : the letter crosses to the left of the block) by
  * a table rule B + [x] -> [x'] + B (e.g. (f3), (f4), (18) read suitably);
  * crossing B letter by letter, each step an exchange or a two-letter semantic window
    (Prover.pass_left);
  * for x a swap: x written by its definition (8) (a semantic window), each of its nine
    letters crossed, and the result written back as one swap.
and symmetrically leftwards.
"""
import letters as LT

DEF_S = lambda j: [('C', j), ('H', j + 1), ('H', j), ('C', j), ('H', j + 1), ('H', j),
                   ('C', j), ('H', j + 1), ('H', j)]


class Pusher:
    def __init__(self, prover):
        self.pr = prover
        self.eng = prover.eng

    def cross(self, w, i, B, left):
        """B at w[i:i+n].  left=False: the letter after B crosses to before it; left=True:
        the letter before B crosses to after it.  Returns (steps, w', i') or None, i' the
        new position of B."""
        n = len(B)
        w = list(w)
        if not left:
            if i + n >= len(w):
                return None
            x = w[i + n]
            # rules
            for k, (l, r) in enumerate(self.eng.table):
                for d in (False, True):
                    a, b = (r, l) if d else (l, r)
                    if len(a) == n + 1 and a[:n] == B and w[i:i + n + 1] == a and b[1:] == B:
                        return [('rw', i, k, d)], w[:i] + b + w[i + n + 1:], i + 1
            # letter by letter
            steps = []
            cur = list(w)
            ok = True
            for k in range(i + n - 1, i - 1, -1):
                r = self.pr.pass_left(cur[k], cur[k + 1])
                if r is None:
                    ok = False
                    break
                if r[0] == 'sw':
                    steps.append(('sw', k))
                    cur[k], cur[k + 1] = cur[k + 1], cur[k]
                else:
                    steps.append(('sem', k, 2, [r[1], r[2]]))
                    cur[k], cur[k + 1] = r[1], r[2]
            if ok and cur[i + 1:i + 1 + n] == B:
                return steps, cur, i + 1
            # a swap: by its definition
            if x[0] == 'S':
                D = DEF_S(x[1])
                steps = [('sem', i + n, 1, D)]
                cur = w[:i + n] + D + w[i + n + 1:]
                j = i
                for t in range(len(D)):
                    r = self.cross(cur, j, B, False)
                    if r is None:
                        return None
                    st, cur, j = r
                    steps += st
                # the crossed letters are cur[i:j]; write them back as one swap
                seg = cur[i:j]
                for y in ('S',):
                    for jj in range(2):
                        if self.eng.sem_ok(seg, [('S', jj)]):
                            steps.append(('sem', i, len(seg), [('S', jj)]))
                            cur = cur[:i] + [('S', jj)] + cur[j:]
                            return steps, cur, i + 1
                return None
            return None
        else:
            if i == 0:
                return None
            x = w[i - 1]
            for k, (l, r) in enumerate(self.eng.table):
                for d in (False, True):
                    a, b = (r, l) if d else (l, r)
                    if len(a) == n + 1 and a[1:] == B and w[i - 1:i + n] == a and b[:n] == B:
                        return [('rw', i - 1, k, d)], w[:i - 1] + b + w[i + n:], i - 1
            steps = []
            cur = list(w)
            ok = True
            for k in range(i - 1, i + n - 1):
                # cur[k] (the travelling letter) moves right past cur[k + 1]
                r = self.pr.pass_left(cur[k], cur[k + 1])
                if r is None:
                    ok = False
                    break
                if r[0] == 'sw':
                    steps.append(('sw', k))
                    cur[k], cur[k + 1] = cur[k + 1], cur[k]
                else:
                    steps.append(('sem', k, 2, [r[1], r[2]]))
                    cur[k], cur[k + 1] = r[1], r[2]
            if ok and cur[i - 1:i - 1 + n] == B:
                return steps, cur, i - 1
            if x[0] == 'S':
                D = DEF_S(x[1])
                steps = [('sem', i - 1, 1, D)]
                cur = w[:i - 1] + D + w[i:]
                j = i - 1 + len(D)
                for t in range(len(D)):
                    r = self.cross(cur, j, B, True)
                    if r is None:
                        return None
                    st, cur, j = r
                    steps += st
                seg = cur[j + n:j + n + len(D)]
                for jj in range(2):
                    if self.eng.sem_ok(seg, [('S', jj)]):
                        steps.append(('sem', j + n, len(D), [('S', jj)]))
                        cur = cur[:j + n] + [('S', jj)] + cur[j + n + len(D):]
                        return steps, cur, j
                return None
            return None

    def push(self, w, i, B, left, stop=None):
        """Push B as far as it goes (or to position `stop`); returns (steps, w', i')."""
        steps = []
        while True:
            if stop is not None and i == stop:
                break
            r = self.cross(w, i, B, left)
            if r is None:
                break
            st, w, i = r
            steps += st
        return steps, w, i
