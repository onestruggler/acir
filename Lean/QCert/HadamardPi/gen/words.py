from deriv import H, X, Z, fmt
from good4 import good
D02 = [H(2,3), H(1,3), H(0,2), H(2,3), H(0,1), H(1,3)]
D13 = [H(2,3), H(1,3), H(0,2), H(2,3), H(0,1), H(0,2)]
D23 = [H(2,3), H(0,1)]
def words():
    W = {}
    for par in (0, 1):
        W[((0,1), par)] = []
        W[((2,3), par)] = D23
    W[((0,2), 0)] = D02
    W[((1,3), 0)] = D13
    W[((0,3), 0)] = [X(2,3)] + D02 + [X(2,3)]
    W[((1,2), 0)] = [X(2,3)] + D13 + [X(2,3)]
    W[((0,2), 1)] = [Z(3)] + W[((0,2), 0)] + [Z(3)]
    W[((1,3), 1)] = [Z(2)] + W[((1,3), 0)] + [Z(2)]
    W[((0,3), 1)] = [Z(2)] + W[((0,3), 0)] + [Z(2)]
    W[((1,2), 1)] = [Z(3)] + W[((1,2), 0)] + [Z(3)]
    return W
if __name__ == "__main__":
    from q2 import matrix
    for (A, par), D in words().items():
        w = D + [H(*A)]
        assert matrix(w, 4) == matrix([H(0,1)], 4), (A, par)
        res = []
        for k in range(len(D) + 1):
            g = good(w[k:], par)
            res.append('-' if g is None else ('?' if g[1] is None else str(g[1])))
        print(A, par, fmt(D), ''.join(res))
