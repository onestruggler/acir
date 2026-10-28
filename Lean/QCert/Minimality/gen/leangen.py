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

SLIDES = False   # set by a generator to write runs of exchanges as one `.slide`

def compress(steps):
    """Runs of exchanges moving one generator: `swap i, swap i-1, …, swap m` moves the
    generator at `i + 1` to `m`, `swap i, swap i+1, …, swap M` the one at `i` to `M + 1`."""
    out = []
    k = 0
    while k < len(steps):
        st = steps[k]
        if st[0] != 'swap':
            out.append(st); k += 1; continue
        j = k
        while j + 1 < len(steps) and steps[j + 1][0] == 'swap' and steps[j + 1][1] == steps[j][1] - 1:
            j += 1
        if j > k:
            out.append(('slide', st[1] + 1, steps[j][1])); k = j + 1; continue
        while j + 1 < len(steps) and steps[j + 1][0] == 'swap' and steps[j + 1][1] == steps[j][1] + 1:
            j += 1
        if j > k:
            out.append(('slide', st[1], steps[j][1] + 1)); k = j + 1; continue
        out.append(st); k += 1
    return out

def lean_steps(steps):
    out = []
    for st in (compress(steps) if SLIDES else steps):
        if st[0] == 'swap': out.append('.swap %d' % st[1])
        elif st[0] == 'slide': out.append('.slide %d %d' % (st[1], st[2]))
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

    def proof_named(self, eqs, steps_name, indent=4):
        return 'derive hsc\n%s%s\n%s%s\n%s(by decide +kernel)' % (
            ' ' * indent, fmt_list([self.eq(e) for e in eqs], indent),
            ' ' * indent, steps_name, ' ' * indent)

    def steps_def(self, name, steps, doc):
        ls = lean_steps(steps)
        chunks = [fmt_list(ls[i:i + 400], 4) for i in range(0, len(ls), 400)]
        return '/-- %s -/\ndef %s : List Step :=\n  %s\n' % (doc, name, ' ++\n  '.join(chunks))

def word(letters, lname):
    """A time-order word as `tw n [...]`."""
    return '[' + ', '.join('(.%s, %d)' % (lname[g], o) for (g, o) in letters) + ']'
