import pickle
from fractions import Fraction as F
from tree import S, mat_mul, word_matrix
from tree2 import key
dist, reps = pickle.load(open("ball2.pkl", "rb"))

def from_rows(rows):  # rows[i][j] = (a, b) Fractions; cols[j][i]
    return [[(int(rows[i][j][0] * S), int(rows[i][j][1] * S)) for i in range(8)] for j in range(8)]

def K(abcd):
    h = [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]]
    rows = [[(F(1 if i == j else 0), F(0)) for j in range(8)] for i in range(8)]
    for x, i in enumerate(abcd):
        for y, j in enumerate(abcd):
            rows[i][j] = (F(h[x][y], 2), F(0))
    return from_rows(rows)

def M(a):
    rows = [[(F(1 if i == j else 0), F(0)) for j in range(8)] for i in range(8)]
    rows[a][a] = (F(-1), F(0))
    return from_rows(rows)

def d(Mx):
    return dist.get(key(Mx), (">2",))[0]

print("K0123", d(K((0, 1, 2, 3))))
print("K0145", d(K((0, 1, 4, 5))))
print("K0246", d(K((0, 2, 4, 6))))
print("K0124", d(K((0, 1, 2, 4))))
print("K0127", d(K((0, 1, 2, 7))))
print("K0123 M0", d(mat_mul(K((0, 1, 2, 3)), M(0))))
print("M0", d(M(0)))
print("K0123 M0 M1", d(mat_mul(mat_mul(K((0, 1, 2, 3)), M(0)), M(1))))
for a in range(4):
    print("K0123 M", a, d(mat_mul(K((0, 1, 2, 3)), M(a))))
