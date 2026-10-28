"""Signed permutations: semantics of words over N, X and canonical words."""
from fractions import Fraction as F
from alg import ident, word_apply
from rules import N, X

def as_sp(M):
    """M as (pi, sg) with M e_j = sg[j] e_{pi[j]}, or None."""
    n = len(M)
    pi, sg = [None] * n, [None] * n
    for j in range(n):
        nz = [(i, M[i][j]) for i in range(n) if M[i][j] != 0]
        if len(nz) != 1 or abs(nz[0][1]) != 1:
            return None
        pi[j], sg[j] = nz[0][0], int(nz[0][1])
    return pi, sg

def sp_word(M):
    """A word over N, X (rightmost first) with matrix M (a signed permutation):
    first the signs (on the source indices), then a product of transpositions."""
    n = len(M)
    pi, sg = as_sp(M)
    # M = P_pi * D_sg where D_sg = diag(sg); word = (transpositions for P_pi) ++ (N_j for sg_j=-1)
    signs = [N(j) for j in range(n) if sg[j] == -1]
    # decompose P_pi into transpositions: build word w with matrix P_pi (w applied rightmost first)
    perm = list(pi)  # perm[j] = image of j
    trans = []
    # selection: P_pi = t_1 t_2 ... ; we compute by making perm the identity by left-multiplying swaps
    cur = list(perm)
    while True:
        bad = [j for j in range(n) if cur[j] != j]
        if not bad:
            break
        j = bad[0]
        i = cur[j]  # image of j is i; apply swap (i, j) on the left: new image of j is j
        a, b = min(i, j), max(i, j)
        trans.append(X(a, b))
        cur = [(b if x == a else a if x == b else x) for x in cur]
    # swaps applied on the left: X_t ... X_1 P_pi = I  => P_pi = X_1 ... X_t
    w = tuple(trans) + tuple(signs)
    assert word_apply(list(w), ident(n)) == M, (M, w)
    return w
