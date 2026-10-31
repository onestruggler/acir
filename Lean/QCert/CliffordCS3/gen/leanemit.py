"""Lean emission helpers: word literals, packed certificates (`QCert.CliffordT2.FastRewrite`:
a step is 2 (4096 pos + rule) + dir, 25 bits, chunks of at most 2000 steps), and rule tables."""

CHUNK = 2000
import sys
sys.set_int_max_str_digits(0)


def pack(steps):
    """steps: [(pos, rule_index, forward)] -> [(n, code)] chunks."""
    out = []
    for i in range(0, len(steps), CHUNK):
        ch = steps[i:i + CHUNK]
        code = 0
        for j, (p, r, d) in enumerate(ch):
            assert p < 4096 and r < 4096, (p, r)
            s = 2 * (4096 * p + r) + (1 if d else 0)
            code |= s << (25 * j)
        out.append((len(ch), code))
    return out


def fmt_chunks(chunks):
    return '[' + ', '.join('(%d, %d)' % c for c in chunks) + ']'


def fmt_list(items, per_line=None):
    return '[' + ', '.join(items) + ']'


def wrap(s, indent, width=100):
    """Wrap a long comma-separated Lean term."""
    if len(s) + indent <= width:
        return s
    out = []
    line = ''
    for tok in s.split(', '):
        add = (', ' if line else '') + tok
        if len(line) + len(add) + indent > width and line:
            out.append(line + ',')
            line = tok
        else:
            line += add
    out.append(line)
    return ('\n' + ' ' * indent).join(out)


class RuleEmitter:
    """Emits the needed equations of a proof table as `Rule Γ` definitions.

    sides(k) -> (lhs, rhs) on the emitted alphabet; steps(k) -> [(pos, k', fwd)] on it (or
    None for an axiom); axiom(k) -> a Lean term of type `Rule Γ`."""

    def __init__(self, prefix, rule_type, bounds, inj, fmt_letter, sides, steps, axiom):
        self.prefix = prefix
        self.rule_type = rule_type
        self.bounds = bounds
        self.inj = inj
        self.fmt_letter = fmt_letter
        self.sides = sides
        self.steps = steps
        self.axiom = axiom
        self.names = {}

    def word(self, w):
        return '[' + ', '.join(self.fmt_letter(a) for a in w) + ']'

    def name(self, k):
        return self.names[k]

    def emit(self, k):
        """Lean source of the definition of equation k (all its references emitted before)."""
        nm = '%s%d' % (self.prefix, k)
        self.names[k] = nm
        st = self.steps(k)
        if st is None:
            return 'def %s : %s := %s\n' % (nm, self.rule_type, self.axiom(k))
        refs = []
        idx = {}
        packed = []
        for (p, kk, d) in st:
            if kk not in idx:
                idx[kk] = len(refs)
                refs.append(kk)
            packed.append((p, idx[kk], d))
        l, r = self.sides(k)
        reflist = wrap(', '.join(self.names[kk] for kk in refs), 4)
        return ('def %s : %s :=\n  Rule.byChunks %s %s [%s]\n    %s\n    %s\n    %s (by decide +kernel)\n'
                % (nm, self.rule_type, self.bounds, self.inj, reflist,
                   wrap(self.word(l), 4), wrap(self.word(r), 4), fmt_chunks(pack(packed))))
