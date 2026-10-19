"""Agda spellings of words (shared by the emitters)."""

NAT = {'X0': 'x₀', 'X1': 'x₁', 'X2': 'x₂', 'CX0': 'cx₀', 'CX1': 'cx₁',
       'HH0': 'hh₀', 'HH1': 'hh₁', 'CCX0': 'ccx₀'}
ALN = {'X0': 'ax₀', 'X1': 'ax₁', 'X2': 'ax₂', 'CX0': 'acx₀', 'CX1': 'acx₁',
       'HH0': 'ahh₀', 'HH1': 'ahh₁'}
WLN = {'X0': 'wx₀', 'X1': 'wx₁', 'X2': 'wx₂', 'CX0': 'wcx₀', 'CX1': 'wcx₁',
       'CCX0': 'wccx', 'CXr0': 'wcr₀', 'CXr1': 'wcr₁', 'Z1': 'wz₁'}


def nat(w):
    """a Natural word (tuple of tokens) as ⟪ list ⟫"""
    if not w:
        return 'ε'
    return '⟪ ' + ' ∷ '.join(NAT[t] for t in w) + ' ∷ [] ⟫'


def alist(w):
    if not w:
        return '[]'
    return '(' + ' ∷ '.join(ALN[t] for t in w) + ' ∷ [])'


def wlist(w):
    if not w:
        return '[]'
    return '(' + ' ∷ '.join(WLN[t] for t in w) + ' ∷ [])'
