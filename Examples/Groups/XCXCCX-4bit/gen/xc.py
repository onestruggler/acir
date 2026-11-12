"""Model of {X, CX, CCX} circuits as in Examples/Groups/XCXCCX-4bit.

Letters are (kind, shift): kind in X, CX, CCX, SW; the letter acts on
wires shift .. shift+arity-1, wire 0 the bottom one.  CX: wire s ^= wire
s+1.  CCX: wire s ^= wire s+1 & wire s+2.  SW swaps wires s, s+1.
Words are tuples of letters in diagram order (head acts first).
States are ints, bit w = wire w.
"""
ARITY = {'X': 1, 'CX': 2, 'SW': 2, 'CCX': 3}


def bit(x, w):
    return (x >> w) & 1


def act_letter(l, x):
    k, s = l
    if k == 'X':
        return x ^ (1 << s)
    if k == 'CX':
        return x ^ (bit(x, s + 1) << s)
    if k == 'CCX':
        return x ^ ((bit(x, s + 1) & bit(x, s + 2)) << s)
    if k == 'SW':
        a, b = bit(x, s), bit(x, s + 1)
        return (x & ~(3 << s)) | (b << s) | (a << (s + 1))
    raise ValueError(k)


def perm(word, n):
    out = []
    for x in range(2 ** n):
        for l in word:
            x = act_letter(l, x)
        out.append(x)
    return tuple(out)


def up(word, k=1):
    return tuple((kd, s + k) for kd, s in word)


X = (('X', 0),)
CX = (('CX', 0),)
CCX = (('CCX', 0),)
SW = (('SW', 0),)


def cat(*ws):
    out = ()
    for w in ws:
        out += tuple(w)
    return out


CXd = cat(SW, CX, SW)            # control 0, target 1
CCXd = cat(SW, CCX, SW)          # controls 2,0 target 1
CCX320 = cat(SW, up(CCX), SW)    # controls 3,2 target 0

RULES = {
    'r1': (1, cat(X, X), ()),
    'r2': (2, cat(CX, up(X), CX, up(X)), X),
    'r3': (2, cat(CX, CXd, CX), SW),
    'r4': (3, cat(CCX, up(X, 2), CCX, up(X, 2)), CX),
    'r5': (3, cat(up(SW), CCX, up(SW)), CCX),
    'r6': (3, cat(CXd, CCX, CXd), cat(CCXd, CCX, CCXd)),
    'r7': (4, cat(up(CCX), CX, up(CCX)), cat(CCX320, CX)),
}

if __name__ == '__main__':
    for name, (n, l, r) in RULES.items():
        print(name, perm(l, n) == perm(r, n))
