"""Greylyn's relations for U_n(ℤ[1/√2, i]) (Table 3.1, as
Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics), at n = 2: the
1-qubit Clifford+T operators, on the two basis states.  Words in
operator order over w0, w1 (the phase ω on one basis state), X01, H01;
the instances that need three or four distinct indices do not exist at
n = 2.  The decoding into CliffT₂ on one wire reads a word letter for
letter (every matrix is symmetric, so no reversal is needed): ω on |1⟩
is T, ω on |0⟩ is X T X, and X, H are themselves."""

W0, W1, X, H = 'w0', 'w1', 'X01', 'H01'

R = {
    'order-ω₀': ([W0] * 8, []),
    'order-ω₁': ([W1] * 8, []),
    'order-H': ([H, H], []),
    'order-X': ([X, X], []),
    'comm-ωω₀₁': ([W0, W1], [W1, W0]),
    'comm-ωω₁₀': ([W1, W0], [W0, W1]),
    'swap-Xω': ([X, W1], [W0, X]),
    'swap-Xω′': ([X, W0], [W1, X]),
    'scalar-X': ([W0, W1, X], [X, W0, W1]),
    'scalar-H': ([W0, W1, H], [H, W0, W1]),
    'rel-18': ([H, X], [W1] * 4 + [H]),
    'rel-19': ([H] + [W0] * 2 + [H], [W0] * 6 + [H] + [W0] * 3 + [W1] * 5),
}

DEC = {W0: 'X0 T0 X0', W1: 'T0', X: 'X0', H: 'H0'}


def text(word):
    return ' '.join(DEC[x] for x in word)
