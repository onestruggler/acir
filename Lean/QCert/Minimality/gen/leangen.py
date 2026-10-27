"""Write derivations found by the search as Lean `DEqn`s replayed by `derive`."""

def fmt_list(items, indent):
    line = ''
    lines = []
    for i, it in enumerate(items):
        piece = it + (', ' if i < len(items) - 1 else '')
        if len(line) + len(piece) > 88:
            lines.append(line.rstrip()); line = ''
        line += piece
    lines.append(line)
    return '[' + ('\n' + ' ' * indent).join(lines) + ']'

def lean_steps(steps):
    out = []
    for st in steps:
        if st[0] == 'swap': out.append('.swap %d' % st[1])
        else: out.append('.rw %d %d %s' % (st[1], st[2], 'true' if st[3] else 'false'))
    return out

class Gen:
    def __init__(self, sym_names, scalar_gate, lemma_ident, base='pres.Base fun _ => True'):
        self.sym_names = sym_names          # 'invol' -> 'Sym.invol', ...
        self.scalar_gate = scalar_gate      # Lean name of the scalar gate, e.g. 'Gate.ω'
        self.lemma_ident = lemma_ident      # lemma name -> Lean identifier
        self.base = base

    def eq(self, e):
        kind = e[0]
        if kind == 'ax':
            return 'DEqn.inst (P := pres) (S := fun _ => True) Ax.%s trivial %d %d' % (e[1], e[2], e[3])
        if kind == 'sym':
            return 'DEqn.sym (P := pres) (S := fun _ => True) %s %d %d' % (self.sym_names[e[1]], e[2], e[3])
        if kind == 'lem':
            return '%s.place %d %d' % (self.lemma_ident(e[1]), e[2], e[3])
        if kind == 'scal':
            return 'DEqn.scal (Base := %s) %s %d %d' % (self.base, self.scalar_gate, e[2], e[3])
        raise Exception(e)

    def proof(self, eqs, steps, indent=4):
        return 'derive hsc\n%s%s\n%s%s\n%s(by decide +kernel)' % (
            ' ' * indent, fmt_list([self.eq(e) for e in eqs], indent),
            ' ' * indent, fmt_list(lean_steps(steps), indent), ' ' * indent)

def word(letters, lname):
    """A time-order word as `tw n [...]`."""
    return '[' + ', '.join('(.%s, %d)' % (lname[g], o) for (g, o) in letters) + ']'
