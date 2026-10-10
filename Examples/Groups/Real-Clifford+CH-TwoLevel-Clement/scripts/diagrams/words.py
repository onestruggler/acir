"""The relations as letter lists (operator order)."""
H = lambda a, b: ('H', a, b)
X = lambda a, b: ('X', a, b)
Z = lambda a: ('Z', a)

C0, C1 = [H(0, 1)], [H(2, 3)]
A = [H(0, 2), H(1, 3)]
S0 = [Z(0), Z(1)]
# (20) at 0..3
L20 = C0 + A + C0 + S0 + A
R20 = A + C0 + S0 + A + C0
# (d3) at a<b<c<d = 0<1<2<3
Ld3 = (C1 + A) * 4
Rd3 = C0 + C1
# (f1) = Clement (19) at (0,1,2,3)
Lf1 = C0 + C1 + A
Rf1 = A + C0 + C1
# six indices: blocks (0,1), (2,3), (4,5)
A1 = [H(0, 2), H(1, 3)]
A2 = [H(0, 4), H(1, 5)]
A12 = [H(2, 4), H(3, 5)]
Sig = [X(2, 4), X(3, 5)]
L21 = C0 + A1 + A2 + C0 + S0 + A2 + A1
R21 = A1 + A2 + C0 + S0 + A2 + A1 + C0
Ld4 = (A1 + C0 + A1 + Sig) * 3
Rd4 = A12 + [H(4, 5)] + A12 + Sig
