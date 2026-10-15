"""Write found derivations as Agda Engine terms."""

LETTER = {
    'X0': 'X₀', 'X1': 'X₁', 'X2': 'X₂', 'Z0': 'Z₀', 'Z1': 'Z₁', 'Z2': 'Z₂',
    'CX01': 'CX₀₁', 'CX02': 'CX₀₂', 'CX10': 'CX₁₀', 'CX12': 'CX₁₂', 'CX20': 'CX₂₀', 'CX21': 'CX₂₁',
    'CZ01': 'CZ₀₁', 'CZ02': 'CZ₀₂', 'CZ12': 'CZ₁₂',
    'CCX01': 'CCX₀₁', 'CCX02': 'CCX₀₂', 'CCX12': 'CCX₁₂', 'K01': 'K₀₁', 'K12': 'K₁₂',
    'SW01': 'SW₀₁', 'SW02': 'SW₀₂', 'SW12': 'SW₁₂', 'NK': 'NK', 'CCZ': 'CCZ', 'H2': 'H₂',
}


def agda_name(n, axioms=()):
    if n in axioms:
        return 'e-' + n
    return n.replace('_', '-')


def alist(w):
    return ' ∷ '.join([LETTER[l] for l in w] + ['[]'])


def eq_term(name, o, axioms):
    if isinstance(name, tuple):
        _, base, k, m = name
        t = 'rot⁼ %d %d %s' % (k, m, agda_name(base, axioms))
        return '(sym⁼ (%s))' % t if o == -1 else '(%s)' % t
    t = agda_name(name, axioms)
    return '(sym⁼ %s)' % t if o == -1 else t


def derivation(name, u, v, steps, axioms, indent='  '):
    n = agda_name(name, axioms)
    lines = ['%s : Eqn' % n,
             '%s = derive' % n,
             indent + '(' + alist(u) + ')',
             indent + '(' + alist(v) + ')']
    if not steps:
        lines.append(indent + '[]')
    else:
        for j, (i, nm, o) in enumerate(steps):
            pre = '( ' if j == 0 else '∷ '
            lines.append(indent + pre + 'rw %d %s' % (i, eq_term(nm, o, axioms)))
        lines.append(indent + '∷ [])')
    lines.append(indent + 'Eq.refl')
    return '\n'.join(lines)
