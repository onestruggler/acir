# Separated commutation for the hybrid gadget at four wires.
#
# Barenco's B = L_cw(V^2_t) (black on c) and the white-controlled Barenco
# G = X_c L_cz(V^2_t) X_c of the same V commute group by group: G's white
# units pass B in one window, its CX(c,z) passes B's letters by windows,
# and its controlled V's on (z, t) pass B's controlled V's on (c, t) and
# (w, t) because powers of one V commute.  Conjugating G by white units on
# t and multiplying (three-wire windows) gives L_{not-c, z}(beta_t) for
# every beta in 2T, among them i X: so B commutes with the white Toffoli
# Toff(t; not-c, z), which was the candidate fourth rule (t_bartof.py).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, supp
import passes as P
from passes import L
from blocks import BD
from dec import barenco

def bar(t, c, w, wv='SSKS'):
    """Barenco's L_cw(V^2_t), V spelled wv."""
    return norm(barenco(wv, c, w, t))

def groups_of_bar(t, c, w):
    """the Barenco word's groups: C_c(V)_t, CX(c,w), C_w(V^-1)_t, CX(c,w), C_w(V)_t."""
    b = bar(t, c, w)
    out = []; i = 0
    # cut at the CX letters
    cx = [k for k, g in enumerate(b) if g[0] == 'CX']
    a, bb = cx
    return [b[:a], [b[a]], b[a + 1:bb], [b[bb]], b[bb + 1:]]

def white(c, word): return [('X', c)] + list(word) + [('X', c)]

def pass_groups(name, A_groups, B_groups):
    """A B -> B A, A and B given as lists of groups, each A group passing
    each B group by one window (three wires) or by being disjoint."""
    A = [g for gr in A_groups for g in gr]; Bw = [g for gr in B_groups for g in gr]
    if name in L: return name
    d = Derivation(name, A + Bw, Bw + A, L)
    # bubble B's groups leftward through A's groups, last A group first
    pos_a = [sum(len(x) for x in A_groups[:i]) for i in range(len(A_groups))]
    cur_a = list(A_groups); cur = 0
    off = len(A)
    for bg in B_groups:
        # bg sits at offset off (right after A); move it left past each A group
        p = off
        if len(supp(A) | supp(bg)) <= 3:                  # bg passes all of A in one window
            d.win(p - len(A), p + len(bg), list(bg) + list(A))
            off += len(bg); continue
        for ag in reversed(cur_a):
            p -= len(ag)
            seg = list(ag) + list(bg)
            if not (supp(ag) & supp(bg)):
                for k in range(len(ag) - 1, -1, -1):
                    for j in range(len(bg)): d.comm(p + k + j)
            else:
                assert len(supp(ag) | supp(bg)) <= 3, (show(ag), show(bg))
                d.win(p, p + len(seg), list(bg) + list(ag))
        off += len(bg)
        cur_a = cur_a
        # the A groups now sit after bg: shift the offset base
    d.done(); return name

if __name__ == '__main__':
    t, c, w, z = 0, 1, 2, 3
    Bg = groups_of_bar(t, c, w)
    Gg = groups_of_bar(t, c, z)
    # the white Barenco's groups: X_c conjugates the c-controlled groups;
    # the X letters themselves are absorbed: X_c . C_c(V) . CX(c,z) . C_z . CX . C_z . X_c
    # = [X_c C_c(V) X_c] [X_c CX(c,z) X_c] C_z [X_c CX X_c] C_z
    Gw = [white(c, Gg[0]), white(c, Gg[1]), Gg[2], white(c, Gg[3]), Gg[4]]
    B = [g for gr in Bg for g in gr]; Gl = [g for gr in Gw for g in gr]
    print('B G = G B semantically:', fp(B + Gl) == fp(Gl + B))
    n = pass_groups('B passes white G', Bg, Gw)
    print('derived:', n, len(L[n][0]))

def inv_groups(groups): return [norm(inv(list(g))) for g in reversed(groups)]

def unit_white(c, x, letters):
    """X_c (letters on x controlled by c) X_c, as one group."""
    return white(c, letters)

def bar_tof(t=0, c=1, w=2, z=3):
    """B = L_cw(V^2_t) passes the white Toffoli X_c Toff(t; c, z) X_c."""
    name = f'B{c}{w}>{t} passes Toff{t} not{c} {z}'
    if name in L: return name
    Bg = groups_of_bar(t, c, w)
    Gg = groups_of_bar(t, c, z)
    G = [white(c, Gg[0]), white(c, Gg[1]), Gg[2], white(c, Gg[3]), Gg[4]]
    Gi = inv_groups(G)
    U = [white(c, [('CS', c, t)] * 3)]                         # Lambda_not-c(S^3_t)
    Ui = inv_groups(U)
    Szi = [white(c, [('CSd', c, z)])]                          # Lambda_not-c(S_z)^-1
    E = Szi + Gi + U + Gi + Ui                                 # = Toff(t; not-c, z), white
    Ew = [g for gr in E for g in gr]
    T = [('X', c), ('TOFF', t, c, z), ('X', c)]
    assert fp(norm(Ew)) == fp(norm(T)), 'expansion'
    inner = pass_groups(f'B{c}{w}>{t} passes white iX via V2 conjugates {z}', Bg, E)
    B = [g for gr in Bg for g in gr]
    d = Derivation(name, B + T, T + B, L)
    d.win(len(B), len(B) + 3, Ew)
    d.lemma(inner, 0)
    d.win(0, len(Ew), T)
    d.done(); return name

if __name__ == '__main__':
    n = bar_tof()
    print('candidate rule derived:', n)
    total = 0
    from deriv import BY_NAME
    for k in ('B passes white G', n, 'B12>0 passes white iX via V2 conjugates 3'):
        if k in BY_NAME: total += len(BY_NAME[k].steps); print(' ', k, len(BY_NAME[k].steps), 'steps')
