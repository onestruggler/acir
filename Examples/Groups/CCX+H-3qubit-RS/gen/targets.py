"""All level-0 derivation targets, in dependency order."""
from model import GATES, W, PERM
from rels import R0, T
from perms import shortest_all, pw

TK = [g for g in GATES if g not in ('NK', 'CCZ')]
PG = ['X0', 'X1', 'X2', 'CX01', 'CX02', 'CX10', 'CX12', 'CX20', 'CX21',
      'CCX01', 'CCX02', 'CCX12', 'SW01', 'SW02', 'SW12']
D = shortest_all()


def S(w):
    return ' '.join(D[pw(W(w))])


boot = [
    ('cx10sq', 'CX10 CX10', ''), ('cz01sq', 'CZ01 CZ01', ''),
    ('ccx02sq', 'CCX02 CCX02', ''), ('sw01sq', 'SW01 SW01', ''),
    ('x1sq', 'X1 X1', ''), ('z1sq', 'Z1 Z1', ''), ('cx12sq', 'CX12 CX12', ''),
    ('ccx01sq', 'CCX01 CCX01', ''), ('cx21def', 'K12 CX12 K12', 'CX21'),
    ('cx21sq', 'CX21 CX21', ''), ('cx20def', 'SW01 CX21 SW01', 'CX20'),
    ('cx20sq', 'CX20 CX20', ''), ('sw12sq', 'SW12 SW12', ''),
    ('cx02sq', 'CX02 CX02', ''), ('sw02sq', 'SW02 SW02', ''), ('x2sq', 'X2 X2', ''),
    ('z0def', 'K01 X0 K01', 'Z0'), ('z0sq', 'Z0 Z0', ''), ('z2sq', 'Z2 Z2', ''),
    ('cz02sq', 'CZ02 CZ02', ''), ('cz12sq', 'CZ12 CZ12', ''),
]
A = [
    ('c_x2_cx02', 'X2 CX02', 'CX02 X2'), ('c_x2_cx12', 'X2 CX12', 'CX12 X2'),
    ('c_x2_ccx01', 'X2 CCX01', 'CCX01 X2'), ('c_cx02_cx12', 'CX02 CX12', 'CX12 CX02'),
    ('c_cx02_ccx01', 'CX02 CCX01', 'CCX01 CX02'), ('c_cx12_ccx01', 'CX12 CCX01', 'CCX01 CX12'),
]


def lname(s):
    return s.lower()


table = []
for s in ['SW01', 'SW02', 'SW12', 'X0', 'X1', 'X2']:
    for g in PG:
        if g == s:
            continue
        r = D[pw((s, g, s))]
        if r == (g,) or r == (s, g, s):
            if r == (g,):
                table.append((lname(s) + '_' + lname(g), s + ' ' + g, g + ' ' + s))
            continue
        table.append((lname(s) + '_' + lname(g), s + ' ' + g + ' ' + s, ' '.join(r)))

U = {0: 'X2 CX02 CX12 CCX01', 1: 'CX12 CX21 CCX02 CX12', 2: 'CX12 CCX01',
     3: 'CX01 CX02 CCX12 CX01 CX02', 4: 'CX02 CCX01', 5: 'CX12 CCX02 CX12', 6: 'CCX01'}

comm = []
for i, a in enumerate(PG):
    for b in PG[i + 1:]:
        if pw((a, b)) == pw((b, a)):
            n = 'c_%s_%s' % (a.lower(), b.lower())
            if n not in [t[0] for t in A]:
                comm.append((n, a + ' ' + b, b + ' ' + a))

t3 = [('t3a', 'CCX12 CCX02 CCX12', S('CCX12 CCX02 CCX12'))]
inner = S('CCX12 CCX02 CCX12')
for nm, c in [('t3b', 'X0'), ('t3c', 'CCX01'), ('t3d', 'X0'), ('t3e', 'X2')]:
    w = c + ' ' + inner + ' ' + c
    t3.append((nm, w, S(w)))
    inner = S(w)
t3.append(('T3', ' '.join(T(3)), U[3]))

mid = []
for i in range(6):
    a, b = U[i], U[i + 1]
    m = S(a + ' ' + b + ' ' + a)
    mid += [('br%da' % i, a + ' ' + b + ' ' + a, m), ('br%db' % i, b + ' ' + a + ' ' + b, m),
            ('br%d' % i, a + ' ' + b + ' ' + a, b + ' ' + a + ' ' + b)]
for i in range(7):
    for j in range(i + 2, 7):
        a, b = U[i], U[j]
        m = S(a + ' ' + b)
        mid += [('far%d%da' % (i, j), a + ' ' + b, m), ('far%d%db' % (i, j), b + ' ' + a, m),
                ('far%d%d' % (i, j), a + ' ' + b, b + ' ' + a)]
Tf = [('T%d' % i, ' '.join(T(i)), U[i]) for i in (0, 1, 2, 4, 5)]
orders = [('Usq%d' % i, U[i] + ' ' + U[i], '') for i in range(7)]

TT = lambda i: ' '.join(T(i))
reach = [
    ('cx12r', 'CX12', TT(2) + ' CCX01'),
    ('cx02r', 'CX02', TT(4) + ' CCX01'),
    ('x2r', 'X2', TT(0) + ' CCX01 CX12 CX02'),
    ('ccx02r', 'CCX02', 'CX12 ' + TT(5) + ' CX12'),
    ('cx21r', 'CX21', 'CX12 ' + TT(1) + ' CX12 CCX02'),
    ('cx01r', 'CX01', 'SW12 CX02 SW12'),
    ('ccx12r', 'CCX12', 'CX02 CX01 ' + TT(3) + ' CX02 CX01'),
    ('cx10r', 'CX10', 'CCX12 CX12 CCX12 CX12'),
    ('x0r', 'X0', 'SW02 X2 SW02'),
]
coxT = []
for i in range(7):
    coxT.append(('ordT%d' % i, TT(i) + ' ' + TT(i), ''))
for i in range(6):
    coxT.append(('brT%d' % i, ' '.join([TT(i), TT(i + 1), TT(i)]), ' '.join([TT(i + 1), TT(i), TT(i + 1)])))
for i in range(7):
    for j in range(i + 2, 7):
        coxT.append(('farT%d%d' % (i, j), TT(i) + ' ' + TT(j), TT(j) + ' ' + TT(i)))
