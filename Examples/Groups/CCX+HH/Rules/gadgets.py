"""The controlled gadgets of NaturalP's ctrl construction, checked exactly.

Control on wire 0.  'a' gadgets have the gate directly above the control
and borrow the wire above the gate; 'b' gadgets borrow wire 1 and have
the gate from wire 2 up.  Words are in matrix order (last letter acts
first), letters ('X'|'CX'|'HH'|'SW'|'CCX', position)."""
from synth import apply_word, controlled

def W(s):
    out = []
    for t in s.split():
        k = t.rstrip('0123456789'); out.append((k, int(t[len(k):])))
    return tuple(out)
def up(word, k=1): return tuple((g, i + k) for g, i in word)
def rev(word): return tuple(reversed(word))
def conj(v, u): return v + u + rev(v)

CCXc = W('HH0 CCX0 HH0')                     # Toffoli: controls 0, 2; target 1
V1, V2 = W('CX0 HH0'), W('HH1 CX0 HH0')      # three-wire conjugators (block 0..2)
CHHa = conj(up(V1), CCXc) + conj(up(V2), CCXc)          # control 0, HH 1 2, borrowed 3
# b: control 0, borrowed 1, HH 2 3: conjugate CHHa by the permutation of
# wires 1 2 3 sending (HH 1 2, borrowed 3) to (HH 2 3, borrowed 1).
P3 = W('SW2 SW1')                                       # wire permutation network
CHHb = conj(P3, CHHa)
# Barenco C^3X: controls c, a, b; target t; borrowed beta:
#   T(c,beta;t) T(a,b;beta) T(c,beta;t) T(a,b;beta)
def toffoli_net(perm_net, base):                        # conj of a placed CCX
    return conj(perm_net, base)
# a: control 0, CCX on 1 2 3 (target 1, controls 2 3), borrowed 4
T2a = toffoli_net(W('SW2 SW3 SW2'), W('CCX2'))          # target 4, controls 2 3
T1a = toffoli_net(W('SW0 SW1 SW0 SW3'), W('CCX1'))      # target 1, controls 0 4
C3Xa = T1a + T2a + T1a + T2a
# b: control 0, borrowed 1, CCX on 2 3 4 (target 2, controls 3 4)
T2b = toffoli_net(W('SW1 SW2 SW3 SW2 SW1'), W('CCX2'))  # target 1, controls 3 4
T1b = toffoli_net(W('SW0'), W('CCX1'))                  # target 2, controls 0 1... check
C3Xb = T1b + T2b + T1b + T2b

checks = [
    ('XC', 2, W('HH0 CX0 HH0'), [('X', 1)]),
    ('CCXc', 3, CCXc, [('CX', 1)]),
    ('Fredkin', 3, W('HH0 CCX0 HH1 CCX0 HH1 CCX0 HH0'), [('SW', 1)]),
    ('CHHa', 4, CHHa, [('HH', 1)]),
    ('CHHb', 4, CHHb, [('HH', 2)]),
    ('C3Xa', 5, C3Xa, [('CCX', 1)]),
    ('C3Xb', 5, C3Xb, [('CCX', 2)]),
]
for name, w, word, gate in checks:
    T = controlled(gate, w, 0)
    N = 1 << w
    S = 1 << 12
    ok = all(apply_word(word, e, w) == T(e)
             for e in (tuple(S * int(i == j) for i in range(N)) for j in range(N)))
    print(f'{name:8s} width {w}: {len(word):3d} gates, {"ok" if ok else "WRONG"}')

# ---------------------------------------------------------------------
def network(perm):
    """Adjacent swaps realising the wire permutation perm (list: perm[i]
    is where wire i's content goes), as a list of SW positions applied
    in time order."""
    p = list(perm); w = len(p); sw = []
    # bubble sort the content positions
    cur = list(range(w))           # cur[pos] = content index at pos
    target = [None] * w
    for i, j in enumerate(p): target[j] = i      # position j should hold content i
    for _ in range(w):
        for k in range(w - 1):
            if target.index(cur[k]) > target.index(cur[k + 1]):
                cur[k], cur[k + 1] = cur[k + 1], cur[k]; sw.append(k)
    return sw

def relabel(word, perm, w, gate_ref, target_gate):
    """Find the conjugate of word by the network of perm (either order)
    that implements target_gate controlled on wire 0."""
    sw = network(perm)
    P_time = tuple(('SW', k) for k in sw)          # time order
    P = rev(P_time)                                # matrix order word
    T = controlled(target_gate, w, 0)
    N = 1 << w; S = 1 << 12
    basis = [tuple(S * int(i == j) for i in range(N)) for j in range(N)]
    for cand in (P + word + rev(P), rev(P) + word + P):
        if all(apply_word(cand, e, w) == T(e) for e in basis):
            return cand
    return None

CHHb2 = relabel(CHHa, [0, 2, 3, 1], 4, None, [('HH', 2)])
C3Xb2 = relabel(C3Xa, [0, 2, 3, 4, 1], 5, None, [('CCX', 2)])
print('CHHb', len(CHHb2) if CHHb2 else None)
print('C3Xb', len(C3Xb2) if C3Xb2 else None)
