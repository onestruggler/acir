"""Check the recursive ctrl construction of NaturalP/Ctrl.agda numerically:
ctrl C (control wire 0, C on wires 1..) for single gates of C at every
position, at widths up to 6."""
from synth import apply_word, controlled
from gadgets import W, up, rev, conj, CCXc, CHHa, C3Xa, CHHb2 as CHHb, C3Xb2 as C3Xb

XCg = W('HH0 CX0 HH0')
FRED = W('HH0 CCX0 HH1 CCX0 HH1 CCX0 HH0')
SIG, SIG1 = W('SW0'), W('SW1')

def CTRL(g, j, m):
    """Controlled version of gate g placed at position j of an m-wire
    circuit (so at wires j+1.. of the (m+1)-wire result)."""
    kind = g
    if j == 0:
        a = {'X': 1, 'CX': 2, 'SW': 2, 'HH': 2, 'CCX': 3}[kind]
        room = m - a
        if kind == 'X': return XCg
        if kind == 'CX': return CCXc
        if kind == 'SW': return FRED
        if kind == 'HH': return CHHa if room >= 1 else None
        if kind == 'CCX': return C3Xa if room >= 1 else None
    return CTRL1(g, j - 1, m - 1)

def CTRL1(g, j, m):
    """Control 0, wire 1 spare, gate at position j of an m-wire circuit
    on wires 2.. ((m+2)-wire result)."""
    if j == 0:
        if g == 'HH': return CHHb
        if g == 'CCX': return C3Xb
        return SIG + up(CTRL(g, 0, m + 0)) + SIG       # control 1 -> 0
    inner = CTRL1(g, j - 1, m - 1)
    return W('SW1 SW0') + up(inner) + W('SW0 SW1')

def target(g, j, w):
    return controlled([(g, j + 1)], w, 0)

bad = 0
for m in range(2, 6):           # C has m wires; result has m + 1
    w = m + 1
    for g, a in [('X', 1), ('CX', 2), ('SW', 2), ('HH', 2), ('CCX', 3)]:
        for j in range(0, m - a + 1):
            word = CTRL(g, j, m)
            if word is None:
                continue
            if max(i for _, i in word) + (3 if word[0][0] == 'CCX' else 2) > w + 1:
                pass
            N = 1 << w; S = 1 << 12
            T = target(g, j, w)
            ok = all(apply_word(word, e, w) == T(e)
                     for e in (tuple(S * int(i == k) for i in range(N)) for k in range(N)))
            if not ok:
                bad += 1
                print('WRONG', g, 'at', j, 'width', w)
print('checked; wrong:', bad)
