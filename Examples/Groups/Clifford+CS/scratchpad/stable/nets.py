"""Swap networks placing a 5-wire circuit on chosen wires (LocalPlace.pl).

pl s g = net s . g . net (revS s): net s runs first, so the content of
wire f(i) must reach wire i (i < k) for g's wire i to act on wire f(i).
A network is a list of positions p (the swap of wires p, p+1), in
diagram order.
"""
def bubble(f, n):
    pos = list(range(n))          # pos[c] = current wire of content c
    word = []
    for i, target in enumerate(f):
        p = pos[target]
        while p > i:
            # swap wires p-1, p
            word.append(p - 1)
            a = pos.index(p - 1); b = pos.index(p)
            pos[a], pos[b] = p, p - 1
            p -= 1
    return word

def run(word, n):
    pos = list(range(n))
    for p in word:
        a = pos.index(p); b = pos.index(p + 1)
        pos[a], pos[b] = p + 1, p
    return pos                     # pos[c] = final wire of content c

def places(word, n, k):
    """The wire that base wire i of pl word acts on, i < k."""
    pos = run(word, n)
    return [pos.index(i) for i in range(k)]

def window(f, w, n):
    """tau moving wire w to the top, others in order; rho placing f in n-1."""
    others = [x for x in range(n) if x != w]
    tau = bubble(others, n)
    g = [others.index(x) for x in f]
    rho = bubble(g, n - 1)
    return tau, rho

if __name__ == '__main__':
    n = 7
    for name, f in [('P0', [0,1,2,3,6]), ('P1', [0,1,2,5,6]), ('P2', [0,1,4,5,6]),
                    ('Q0', [2,3,4,5,6]), ('Q1', [0,3,4,5,6]), ('Q2', [0,1,4,5,6])]:
        s = bubble(f, n)
        assert places(s, n, 5) == f, (name, s)
        print(name, f, s)
    for name, f, w in [('P0w4', [0,1,2,3,6], 4), ('P1w4', [0,1,2,5,6], 4),
                       ('P1w3', [0,1,2,5,6], 3), ('P2w3', [0,1,4,5,6], 3),
                       ('Q0w1', [2,3,4,5,6], 1), ('Q1w1', [0,3,4,5,6], 1),
                       ('Q1w2', [0,3,4,5,6], 2), ('Q2w2', [0,1,4,5,6], 2)]:
        tau, rho = window(f, w, n)
        # tau . rho (rho lifted to n wires) places base i at f(i)
        assert places(tau + rho, n, 5) == f, name
        print(name, 'tau', tau, 'rho', rho, 'g', places(rho, n - 1, 5))
