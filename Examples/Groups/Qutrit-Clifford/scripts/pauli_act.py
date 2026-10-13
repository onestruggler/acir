"""The inverse Pauli action (Pauli.agda's act⁻) on the boxes of NormalForm.agda."""
import os
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import re
LETTER = {'𝕟': ('nu',), 'h₀': ('H', 0), 'h₁': ('H', 1), 's₀': ('S', 0), 's₁': ('S', 1), 'c₀': ('CZ', 0)}
src = open(ROOT + '/NormalForm.agda', encoding='utf-8').read()
defs = {}
for line in src.splitlines():
    m = re.match(r'^(\w+ˡ|\w+ \w+)\s+=\s+(.*)$', line)
    if m:
        defs[m.group(1)] = m.group(2)

def ev(expr):
    out = []
    for part in expr.split('++'):
        part = part.strip()
        if part.startswith('map _↥ (') and part.endswith(')'):
            inner = ev(part[len('map _↥ ('):-1])
            out += [t if t[0] == 'nu' else (t[0], t[1] + 1) for t in inner]
            continue
        toks = [t.strip() for t in part.split('∷')]
        for t in toks[:-1]:
            out.append(LETTER[t])
        t = toks[-1]
        if t == '[]': pass
        elif t in LETTER: out.append(LETTER[t])
        elif t.startswith('map _↥ ('): out += ev(t)
        elif t.startswith('(') and t.endswith(')'): out += ev(t[1:-1])
        else: out += ev(defs[t])
    return out

sphi_inv = {0: 0, 1: 0, 2: 1}
def actL_inv(g, P):
    s, ps = P[0], list(P[1])
    if g[0] == 'nu': return (s, ps)
    k = g[1]
    if g[0] == 'H':
        a, b = ps[k]
        return ((s + 2 * a * b) % 3, ps[:k] + [(b, (2 * a) % 3)] + ps[k + 1:])
    if g[0] == 'S':
        a, b = ps[k]
        return ((s + sphi_inv[a]) % 3, ps[:k] + [(a, (b + a) % 3)] + ps[k + 1:])
    if g[0] == 'CZ':
        (a, b), (c, d) = ps[k], ps[k + 1]
        return ((s + 2 * a * c) % 3,
                ps[:k] + [(a, (b + 2 * c) % 3), (c, (d + 2 * a) % 3)] + ps[k + 2:])

def act_inv(word, P):
    for g in word:          # operator order: the leftmost letter's inverse acts first
        P = actL_inv(g, P)
    return P

def box(k, ix):
    return ev(defs['%sl %s%s' % (k, k, ''.join('₀₁₂'[i] for i in ix))])

I, Z, X = (0, 0), (0, 1), (1, 0)
if __name__ == '__main__':
    print('A: act⁻ (0, Z)')
    for a in range(3):
        for b in range(3):
            if (a, b) != (0, 0): print(' A', a, b, act_inv(box('A', (a, b)), (0, [Z, I])))
    print('B: act⁻ (0, I ∷ Z)')
    for a in range(3):
        for b in range(3): print(' B', a, b, act_inv(box('B', (a, b)), (0, [I, Z, I])))
    print('C: act⁻ (0, Z), (0, X)')
    for c in range(3): print(' C', c, act_inv(box('C', (c,)), (0, [Z, I])), act_inv(box('C', (c,)), (0, [X, I])))
    print('D: act⁻ (0, XZ^i ∷ I), (0, Z ∷ I)')
    for a in range(3):
        for b in range(3):
            print(' D', a, b, [act_inv(box('D', (a, b)), (0, [(1, i), I, I])) for i in range(3)],
                  act_inv(box('D', (a, b)), (0, [Z, I, I])))
    print('E: act⁻ (0, X), (0, Z)')
    for e in range(3): print(' E', e, act_inv(box('E', (e,)), (0, [X])), act_inv(box('E', (e,)), (0, [Z])))
    print('F: act⁻ (0, XZ^i), (0, Z)')
    for f in range(3): print(' F', f, [act_inv(box('F', (f,)), (0, [(1, i)])) for i in range(3)], act_inv(box('F', (f,)), (0, [Z])))
