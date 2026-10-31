"""Lean emission helpers: word literals, packed certificates and rule tables.

A step is 2 (4096 pos + rule) + dir, in 25 bits (FastRewrite), or 32 bits
(CliffordCS3.Replay) for long words, in chunks of at most 2000 steps.
"""

CHUNK = 2000
import sys
sys.set_int_max_str_digits(0)


def pack(steps, bits=25):
    """steps: [(pos, rule_index, forward)] -> [(n, code)] chunks."""
    out = []
    for i in range(0, len(steps), CHUNK):
        ch = steps[i:i + CHUNK]
        code = 0
        for j, (p, r, d) in enumerate(ch):
            assert 0 <= p < 2 ** (bits - 13) and 0 <= r < 4096, (p, r)
            s = 2 * (4096 * p + r) + (1 if d else 0)
            code |= s << (bits * j)
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

    def __init__(self, prefix, rule_type, bounds, inj, fmt_letter, sides, steps, axiom,
                 wide=False):
        self.prefix = prefix
        self.rule_type = rule_type
        self.bounds = bounds
        self.inj = inj
        self.fmt_letter = fmt_letter
        self.sides = sides
        self.steps = steps
        self.axiom = axiom
        self.names = {}
        self.wide = wide

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
        replay = 'Rule.byWideChunks' if self.wide else 'Rule.byChunks'
        return ('def %s : %s :=\n  %s %s %s [%s]\n    %s\n    %s\n    %s (by decide +kernel)\n'
                % (nm, self.rule_type, replay, self.bounds, self.inj, reflist,
                   wrap(self.word(l), 4), wrap(self.word(r), 4),
                   fmt_chunks(pack(packed, 32 if self.wide else 25))))
